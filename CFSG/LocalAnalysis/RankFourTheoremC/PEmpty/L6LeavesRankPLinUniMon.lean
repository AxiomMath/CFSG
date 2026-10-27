module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniPerm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup
open scoped commutatorElement

variable {C : Type} [CommGroup C] {n : ℕ}

theorem monT_pow (t : Fin n → C) (k : ℕ) : monT (t ^ k) = (monT t) ^ k :=
  map_pow (SemidirectProduct.inl : (Fin n → C) →* Mon C n) t k

theorem card_entryProd_ker [Finite C] (hn : 1 ≤ n) :
    Nat.card (entryProd C n).ker = Nat.card C ^ (n - 1) := by
  have hsurj : Function.Surjective (entryProd C n) := fun c => by
    refine ⟨Pi.mulSingle ⟨0, hn⟩ c, ?_⟩
    simp [entryProd, Finset.prod_pi_mulSingle']
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [Nat.card_fun, Nat.card_fin] at h1
  have h2 : Nat.card C ^ n = Nat.card C ^ (n - 1) * Nat.card C := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem exists_injective_ker {P : Subgroup (Mon C n)} (hdet : ∀ x ∈ P, monDet x = 1) :
    ∃ g : (monPerm.comp P.subtype).ker → (entryProd C n).ker, Function.Injective g ∧
      ∀ x, ((g x : Fin n → C)) = ((x : P) : Mon C n).left := by
  have hright : ∀ x : (monPerm.comp P.subtype).ker, ((x : P) : Mon C n).right = 1 :=
    fun x => MonoidHom.mem_ker.1 x.2
  have hdetK : ∀ x : (monPerm.comp P.subtype).ker, ∏ i, ((x : P) : Mon C n).left i = 1 := by
    intro x
    have := hdet _ (x : P).2
    rwa [eq_monT_of_right_eq_one (hright x), monDet_monT] at this
  refine ⟨fun x => ⟨((x : P) : Mon C n).left, by
      rw [MonoidHom.mem_ker]
      exact hdetK x⟩, ?_, fun x => rfl⟩
  intro x y hxy
  have h1 : ((x : P) : Mon C n).left = ((y : P) : Mon C n).left := congrArg Subtype.val hxy
  have h2 : ((x : P) : Mon C n) = ((y : P) : Mon C n) := by
    rw [eq_monT_of_right_eq_one (hright x), eq_monT_of_right_eq_one (hright y), h1]
  exact Subtype.ext (Subtype.ext h2)

theorem monT_mem_of_card_le [Finite C] {P : Subgroup (Mon C n)} (hdet : ∀ x ∈ P, monDet x = 1)
    (hcard : Nat.card (entryProd C n).ker ≤ Nat.card (monPerm.comp P.subtype).ker) :
    ∀ t : Fin n → C, ∏ i, t i = 1 → monT t ∈ P := by
  intro t ht
  obtain ⟨g, hinj, hg⟩ := exists_injective_ker hdet
  have hright : ∀ x : (monPerm.comp P.subtype).ker, ((x : P) : Mon C n).right = 1 :=
    fun x => MonoidHom.mem_ker.1 x.2
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨x, hx⟩ := hbij.2 ⟨t, by rw [MonoidHom.mem_ker]; exact ht⟩
  have h1 : ((x : P) : Mon C n).left = t := by
    rw [← hg x, hx]
  have h2 : ((x : P) : Mon C n) = monT t := by
    rw [eq_monT_of_right_eq_one (hright x), h1]
  rw [← h2]
  exact (x : P).2

theorem right_eq_one_of_scalar_comm (hn : 4 ≤ n) {ζ : C} (hζ2 : ζ ^ 2 ≠ 1)
    {P : Subgroup (Mon C n)} (hD : ∀ t : Fin n → C, ∏ i, t i = 1 → monT t ∈ P)
    {x : Mon C n} (hcomm : ∀ u ∈ P, ∃ z : C, ⁅x, u⁆ = monScalar C n z) : x.right = 1 := by
  classical
  by_contra hσ
  set σ : Perm (Fin n) := x.right with hσdef
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  have hcardlt : ({i, σ i, σ.symm i} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    have h3 : ({i, σ i, σ.symm i} : Finset (Fin n)).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ (Finset.card_singleton _).le)))
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  obtain ⟨hmi, hmj, hmk⟩ := hm
  have hji : σ i ≠ i := hi
  have hki : σ.symm i ≠ i := fun h => hi (by
    have := congrArg σ h
    simpa using this.symm)
  let t : Fin n → C := Pi.mulSingle i ζ * Pi.mulSingle m ζ⁻¹
  have ht : ∏ k, t k = 1 := by
    simp only [t, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, if_true]
    exact mul_inv_cancel ζ
  obtain ⟨z, hz⟩ := hcomm (monT t) (hD t ht)
  have hz' : monT ((t ∘ σ.symm) * t⁻¹) = monT (fun _ => z) := by
    rw [← mon_comm_monT, hz, monScalar_apply]
  have hz'' : ∀ k, t (σ.symm k) * (t k)⁻¹ = z := fun k => by
    have := congrFun (monT_injective hz') k
    simpa using this
  have hmi' : m ≠ i := hmi
  have h1 := hz'' (σ i)
  have h2 := hz'' i
  have ht_ji : t (σ i) = 1 := by
    simp [t, Pi.mulSingle_eq_of_ne, hji, Ne.symm hmj]
  have ht_i : t i = ζ := by
    simp [t, Pi.mulSingle_eq_of_ne, hmi'.symm]
  have ht_ki : t (σ.symm i) = 1 := by
    simp [t, Pi.mulSingle_eq_of_ne, hki, Ne.symm hmk]
  rw [Equiv.symm_apply_apply, ht_i, ht_ji, inv_one, mul_one] at h1
  rw [ht_ki, ht_i, one_mul] at h2
  apply hζ2
  have h3 : ζ = ζ⁻¹ := h1.trans h2.symm
  rw [pow_two]
  nth_rewrite 1 [h3]
  exact inv_mul_cancel ζ

theorem exists_diag_lift {f : ℕ} [hf : Fact f.Prime] (hf2 : f ≠ 2) [Finite C] [Nontrivial C]
    [IsCyclic C] (hCf : IsPGroup f C) (hfn : f ∣ n) (hn : 4 ≤ n)
    {P : Subgroup (Mon C n)} (hPp : IsPGroup f P) (hdet : ∀ x ∈ P, monDet x = 1)
    (hcard : Nat.card C ^ (n - 1) * f ^ padicValNat f n.factorial ≤ Nat.card P)
    {x₀ : Mon C n} (hx₀ : x₀ ∈ P) (hcomm : ∀ u ∈ P, ∃ z : C, ⁅x₀, u⁆ = monScalar C n z)
    (hpow : ∃ z : C, x₀ ^ f = monScalar C n z) :
    ∃ (t : Fin n → C) (s : C), x₀ = monT t * monScalar C n s ∧ (∀ i, t i ^ f = 1) ∧
      ∏ i, t i = 1 := by
  classical
  have hn0 : 0 < n := by omega
  let π : P →* Perm (Fin n) := monPerm.comp P.subtype
  have hcardP := Subgroup.card_ker_mul_card_range π
  have hBp : IsPGroup f π.range := hPp.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have hBle : Nat.card π.range ≤ f ^ padicValNat f n.factorial := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hBp
    have hdvd : Nat.card π.range ∣ n.factorial := by
      have := Subgroup.card_subgroup_dvd_card π.range
      rwa [Nat.card_perm, Nat.card_fin] at this
    rw [hk] at hdvd ⊢
    exact Nat.pow_le_pow_right hf.out.pos
      ((padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1 hdvd)
  obtain ⟨g, hginj, -⟩ := exists_injective_ker hdet
  have hkerle : Nat.card π.ker ≤ Nat.card C ^ (n - 1) := by
    rw [← card_entryProd_ker (by omega : 1 ≤ n)]
    exact Nat.card_le_card_of_injective g hginj
  have hv : 0 < f ^ padicValNat f n.factorial := pow_pos hf.out.pos _
  have hDpos : 0 < Nat.card C ^ (n - 1) := pow_pos Nat.card_pos _
  have h1 : Nat.card C ^ (n - 1) ≤ Nat.card π.ker := by
    refine Nat.le_of_mul_le_mul_right ?_ hv
    calc Nat.card C ^ (n - 1) * f ^ padicValNat f n.factorial ≤ Nat.card P := hcard
      _ = Nat.card π.ker * Nat.card π.range := hcardP.symm
      _ ≤ Nat.card π.ker * f ^ padicValNat f n.factorial := Nat.mul_le_mul_left _ hBle
  have h2 : f ^ padicValNat f n.factorial ≤ Nat.card π.range := by
    refine Nat.le_of_mul_le_mul_left ?_ hDpos
    calc Nat.card C ^ (n - 1) * f ^ padicValNat f n.factorial ≤ Nat.card P := hcard
      _ = Nat.card π.ker * Nat.card π.range := hcardP.symm
      _ ≤ Nat.card C ^ (n - 1) * Nat.card π.range := Nat.mul_le_mul_right _ hkerle
  have hBcard : Nat.card π.range = f ^ padicValNat f n.factorial := le_antisymm hBle h2
  have hD : ∀ t : Fin n → C, ∏ i, t i = 1 → monT t ∈ P := by
    refine monT_mem_of_card_le hdet ?_
    rw [card_entryProd_ker (by omega : 1 ≤ n)]
    exact h1
  have hfC : f ∣ Nat.card C := by
    obtain ⟨k, hk, hkc⟩ := hCf.nontrivial_iff_card.1 inferInstance
    rw [hkc]
    exact dvd_pow_self f hk.ne'
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := C) f hfC
  have hζ2 : ζ ^ 2 ≠ 1 := fun h =>
    hf2 ((Nat.prime_dvd_prime_iff_eq hf.out Nat.prime_two).1 (hζ ▸ orderOf_dvd_of_pow_eq_one h))
  have hright : x₀.right = 1 := right_eq_one_of_scalar_comm hn hζ2 hD hcomm
  have hx₀T : x₀ = monT x₀.left := eq_monT_of_right_eq_one hright
  set d : Fin n → C := x₀.left with hd
  obtain ⟨z₀, hz₀⟩ := hpow
  have hdf : ∀ i, d i ^ f = z₀ := by
    have h3 : monT (d ^ f) = monT (fun _ => z₀) := by
      rw [← monScalar_apply, ← hz₀, hx₀T]
      exact monT_pow d f
    intro i
    exact congrFun (monT_injective h3) i
  have hdetd : ∏ i, d i = 1 := by
    have := hdet x₀ hx₀
    rwa [hx₀T, monDet_monT] at this
  let i₀ : Fin n := ⟨0, hn0⟩
  let T : Subgroup C := (powMonoidHom f : C →* C).ker
  have hεT : ∀ k, d k * (d i₀)⁻¹ ∈ T := fun k => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_pow, inv_pow, hdf, hdf, mul_inv_cancel]
  let y : Fin n → T := fun k => ⟨d k * (d i₀)⁻¹, hεT k⟩
  let ℓ : Fin n → ZMod f := fun k => torsionLog hCf (y k)
  have hu : ∀ u ∈ P, ∃ w : C, ∀ k, d (u.right.symm k) = w * d k := by
    intro u hu
    obtain ⟨z, hz⟩ := hcomm u hu
    refine ⟨z⁻¹, fun k => ?_⟩
    have h3 : ⁅u, monT d⁆ = monScalar C n z⁻¹ := by
      rw [← hx₀T, ← commutatorElement_inv, hz, map_inv]
    rw [mon_comm_monT, monScalar_apply] at h3
    have h4 := congrFun (monT_injective h3) k
    simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply] at h4
    rw [← h4]
    group
  have hshift : ∀ u ∈ P, ∃ γ : ZMod f, ∀ k, ℓ (u.right.symm k) = ℓ k + γ := by
    intro u hu'
    obtain ⟨w, hw⟩ := hu u hu'
    have hwy : ∀ k, (y (u.right.symm k) : C) = w * (y k : C) := fun k => by
      change d (u.right.symm k) * (d i₀)⁻¹ = w * (d k * (d i₀)⁻¹)
      rw [hw k, mul_assoc]
    have hwT : w ∈ T := by
      have h5 : w = (y (u.right.symm i₀) : C) * ((y i₀ : T) : C)⁻¹ := by
        rw [hwy i₀]
        group
      rw [h5]
      exact T.mul_mem (y _).2 (T.inv_mem (y i₀).2)
    refine ⟨torsionLog hCf ⟨w, hwT⟩, fun k => ?_⟩
    have h6 : y (u.right.symm k) = ⟨w, hwT⟩ * y k := Subtype.ext (hwy k)
    change torsionLog hCf (y (u.right.symm k)) = torsionLog hCf (y k) + _
    rw [h6, torsionLog_mul, add_comm]
  have hpn : (n : ZMod f) = 0 := (ZMod.natCast_eq_zero_iff n f).2 hfn
  have hsum : ∑ k, ℓ k = 0 := by
    by_cases hnz : ∃ u ∈ P, ∃ γ : ZMod f, γ ≠ 0 ∧ ∀ k, ℓ (u.right.symm k) = ℓ k + γ
    · obtain ⟨u, -, γ, hγ, hsh⟩ := hnz
      exact sum_eq_zero_of_shift hf2 hpn u.right.symm ℓ hγ hsh
    · push Not at hnz
      have hinv : ∀ σ ∈ π.range, ∀ k, ℓ (σ k) = ℓ k := by
        rintro σ ⟨⟨u, hu'⟩, rfl⟩ k
        obtain ⟨γ, hγ⟩ := hshift u⁻¹ (P.inv_mem hu')
        have hγ0 : γ = 0 := by
          by_contra hne
          obtain ⟨k', hk'⟩ := hnz u⁻¹ (P.inv_mem hu') γ hne
          exact hk' (hγ k')
        have h7 : (u⁻¹).right.symm = u.right := by
          rw [SemidirectProduct.inv_right]
          rfl
        rw [h7, hγ0] at hγ
        have h9 := hγ k
        rw [add_zero] at h9
        exact h9
      have hfix : ∀ k : Fin n, ∃ b : π.range, b • k ≠ k := fun k => by
        obtain ⟨σ, hσ, hσk⟩ := exists_moved_of_card hfn hn0 π.range hBcard k
        exact ⟨⟨σ, hσ⟩, hσk⟩
      exact sum_eq_zero_of_isPGroup hBp hfix ℓ (fun b k => hinv b b.2 k)
  have hprod : ∏ k, d k * (d i₀)⁻¹ = 1 := by
    have h8 : ∏ k, y k = 1 := by
      apply torsionLog_injective hCf
      have h0 : torsionLog hCf (1 : T) = 0 := by
        have h9 := torsionLog_mul hCf (1 : T) 1
        rw [mul_one] at h9
        simpa using h9
      rw [torsionLog_prod, hsum, h0]
    have := congrArg Subtype.val h8
    rwa [SubmonoidClass.coe_finset_prod, Subgroup.coe_one] at this
  refine ⟨fun k => d k * (d i₀)⁻¹, d i₀, ?_, fun k => ?_, hprod⟩
  · rw [monScalar_apply, ← monT_mul, hx₀T]
    congr 1
    funext k
    simp
  · have := hεT k
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU
