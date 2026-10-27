module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}

theorem E8ZPkg.e_mul_self (P : E8ZPkg z e E B T A X) : e * e = 1 := by
  have hK : IsPGroup 2 ↥((CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({z} : Set G)))).map
      (Subgroup.centralizer ({z} : Set G)).subtype
  have hee : e * e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype :=
    mul_mem P.e_mem_O2 P.e_mem_O2
  obtain ⟨k, hk⟩ := hK ⟨e * e, hee⟩
  have hk' : (e * e) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  obtain ⟨φ, -, hker, -, hφe⟩ := P.hat
  have heB : e ∈ B := P.E_le_B P.e_mem
  have hα : alpha * alpha = 1 := yamakiSp_mul_self 5
  have hφsq : φ ((⟨e, heB⟩ : ↥B) * ⟨e, heB⟩) = 1 := by
    rw [map_mul, hφe]
    exact Subtype.ext hα
  have hmem_ker : ((⟨e, heB⟩ : ↥B) * ⟨e, heB⟩) ∈ φ.ker := MonoidHom.mem_ker.mpr hφsq
  rw [hker, Subgroup.mem_subgroupOf] at hmem_ker
  have hmem : e * e ∈ oddCoreIn E := hmem_ker
  have hord : orderOf (e * e) ∣ Nat.card (oddCoreIn E) :=
    (oddCoreIn E).orderOf_dvd_natCard hmem
  have hodd_ord : Odd (orderOf (e * e)) := Odd.of_dvd_nat (odd_card_oddCoreIn E) hord
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  have hi0 : i = 0 := by
    by_contra hne
    have hev : Even (orderOf (e * e)) := by
      rw [hi]
      exact Nat.even_pow.mpr ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.mpr hodd_ord) hev
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.mp hi

theorem E8ZPkg.e_mem_T (P : E8ZPkg z e E B T A X) : e ∈ (T : Subgroup G) := by
  have h2 : e ^ 2 = 1 := by
    rw [pow_two]
    exact P.e_mul_self
  have hZ : IsPGroup 2 (Subgroup.zpowers e) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one h2
  have hcomm : ∀ t ∈ (T : Subgroup G), e * t = t * e := fun t ht =>
    Subgroup.mem_centralizer_iff.mp (P.B_le (P.T_le ht)) e (Set.mem_singleton e)
  have hTn : (T : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro t ht
    have hfix : (MulAut.conj t).toMonoidHom e = e := by
      show t * e * t⁻¹ = e
      rw [← hcomm t ht, mul_inv_cancel_right]
    have hmap : (Subgroup.zpowers e).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers e := by
      rw [MonoidHom.map_zpowers, hfix]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hp : IsPGroup 2 ((T : Subgroup G) ⊔ Subgroup.zpowers e : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' T.isPGroup' hZ hTn
  have hmax : (T : Subgroup G) ⊔ Subgroup.zpowers e = (T : Subgroup G) :=
    T.is_maximal' hp le_sup_left
  have he : e ∈ (T : Subgroup G) ⊔ Subgroup.zpowers e :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  rw [hmax] at he
  exact he

theorem E8ZPkg.oddCoreIn_eq_bot (P : E8ZPkg z e E B T A X)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) : oddCoreIn E = ⊥ := by
  have hEC : E ≤ Subgroup.centralizer ({e} : Set G) := P.E_le_B.trans P.B_le
  have hn : (E.subgroupOf (Subgroup.centralizer ({e} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEC]
    intro x k hx hk
    have hmem : (MulAut.conj k).toMonoidHom x ∈ E.map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [P.E_normal k hk] at hmem
    exact hmem
  have hsub : IsSubnormal E (Subgroup.centralizer ({e} : Set G)) :=
    isSubnormal_of_normal_subgroupOf hEC hn
  have hle := oddCoreIn_le_of_isSubnormal hsub
  rw [hodd, le_bot_iff] at hle
  exact hle

theorem E8ZPkg.exists_mulEquiv (P : E8ZPkg z e E B T A X)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥) :
    ∃ φ : ↥B ≃* ↥Hhat, (E.subgroupOf B).map φ.toMonoidHom = E0.subgroupOf Hhat ∧
      φ ⟨e, P.E_le_B P.e_mem⟩ = ⟨alpha, alpha_mem_Hhat⟩ := by
  obtain ⟨φ, hsurj, hker, hE, hφe⟩ := P.hat
  have hEbot : oddCoreIn E = ⊥ := P.oddCoreIn_eq_bot hodd
  have hinj : Function.Injective φ := by
    refine (MonoidHom.ker_eq_bot_iff φ).mp ?_
    rw [hker, hEbot, Subgroup.bot_subgroupOf]
  refine ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, ?_, hφe⟩
  have hcoe : (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).toMonoidHom = φ :=
    MonoidHom.ext fun _ => rfl
  rw [hcoe]
  exact hE

end CFSG.ClassicalInvolution.Sp62Rec
