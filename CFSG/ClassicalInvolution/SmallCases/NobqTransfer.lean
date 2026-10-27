module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria
public import CFSG.Dihedral.BrauerSuzuki.Helpers

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.BrauerSuzuki.Helpers

theorem exists_not_commute_of_mulEquiv_quaternionGroup {P : Type*} [Group P] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (e : P ≃* QuaternionGroup n) : ∃ a b : P, a * b ≠ b * a := by
  refine ⟨e.symm (QuaternionGroup.a 1), e.symm (QuaternionGroup.xa 0), fun h => ?_⟩
  have h1 := congrArg e h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h1
  have h2 : (2 : ZMod (2 * n)) = 0 := by linear_combination (-1 : ZMod (2 * n)) * h1
  have h3 : 2 * n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n)).1 (by exact_mod_cast h2)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_orderOf_eq_two_of_datum {R : Subgroup G} (S : Sylow 2 R) {n : ℕ} [NeZero n]
    (e : (S : Subgroup R) ≃* QuaternionGroup n) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (ht2 : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G)) {u : G} (huR : u ∈ R) (hu : orderOf u = 2) :
    u = t := by
  obtain ⟨t', ht'S, rfl⟩ := ht
  have ht2' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht2
  have hu' : orderOf (⟨u, huR⟩ : R) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hu
  obtain ⟨c, s, hs, hs2, hcs⟩ := exists_conj_mem_sylow_of_orderOf_eq_two S hu'
  have hsq : ∀ x : (S : Subgroup R), orderOf x = 2 → e x = QuaternionGroup.a (n : ZMod (2 * n)) :=
    fun x hx => quat_unique_order_two (by rw [MulEquiv.orderOf_eq]; exact hx)
  have hst : s = t' := by
    have h1 := hsq ⟨s, hs⟩ (by rw [Subgroup.orderOf_mk]; exact hs2)
    have h2 := hsq ⟨t', ht'S⟩ (by rw [Subgroup.orderOf_mk]; exact ht2')
    exact congrArg Subtype.val (e.injective (h1.trans h2.symm))
  have hct : (c : G) * (t' : G) = (t' : G) * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hRC c.2)
  have hc : c * t' = t' * c := Subtype.ext hct
  have : (⟨u, huR⟩ : R) = t' := by
    rw [← hcs, hst]
    calc c * t' * c⁻¹ = t' * c * c⁻¹ := by rw [hc]
      _ = t' := by simp
  exact congrArg Subtype.val this

theorem exists_uniqueInvNormal_of_datum (F : Subgroup G) [F.Normal]
    (hOut : ∀ P : Subgroup (G ⧸ F), IsPGroup 2 P → IsCyclic P)
    {R : Subgroup G} (S : Sylow 2 R) {r : ℕ} (hr : 3 ≤ r)
    (e : (S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
    {t : G} (ht : t ∈ (S : Subgroup R).map R.subtype) (ht2 : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    ∃ htF : t ∈ F, UniqueInvNormal (⟨t, htF⟩ : F) ((R ⊓ F).subgroupOf F) := by
  classical
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hn2 : 2 ≤ 2 ^ (r - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinv : ∀ u ∈ R, orderOf u = 2 → u = t :=
    fun u huR hu => eq_of_orderOf_eq_two_of_datum S e ht ht2 hRC huR hu
  have htR : t ∈ R := by
    obtain ⟨x, -, hx⟩ := ht
    exact hx ▸ x.2
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0
  have hS0le : S0 ≤ R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS0p : IsPGroup 2 S0 := S.isPGroup'.map R.subtype
  have hnc : ∃ a b : S0, a * b ≠ b * a :=
    exists_not_commute_of_mulEquiv_quaternionGroup hn2
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e)
  have hA : ∃ s ∈ S0, s ∈ F ∧ orderOf s = 4 := by
    by_contra hA
    have hcent : ∀ x : S0, (x : G) ∈ F → x ∈ Subgroup.center S0 := by
      intro x hxF
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS0p x
      have hk' : orderOf (x : G) = 2 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      have hk1 : k ≤ 1 := by
        by_contra hk2
        refine hA ⟨(x : G) ^ (2 ^ (k - 2)), S0.pow_mem x.2 _, F.pow_mem hxF _, ?_⟩
        rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
          (by rw [hk']; exact pow_dvd_pow 2 (by omega)), hk', Nat.pow_div (by omega) (by norm_num)]
        have : k - (k - 2) = 2 := by omega
        norm_num [this]
      rw [Subgroup.mem_center_iff]
      intro y
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
      · have : (x : G) = 1 := orderOf_eq_one_iff.mp (by simpa using hk')
        have hx1 : x = 1 := Subtype.ext this
        rw [hx1]
        simp
      · have hxt : (x : G) = t := hinv _ (hS0le x.2) (by simpa using hk')
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp (hRC (hS0le y.2))
        simp only [Subgroup.coe_mul, hxt]
        exact this
    have : IsCyclic (S0.map (QuotientGroup.mk' F)) := hOut _ (hS0p.map _)
    let f : S0 →* S0.map (QuotientGroup.mk' F) :=
      ((QuotientGroup.mk' F).comp S0.subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
    have hf : f.ker ≤ Subgroup.center S0 := by
      intro x hx
      apply hcent
      have h1 : (QuotientGroup.mk' F) (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((f.isMulCommutative_of_isCyclic_of_ker_le_center hf).is_comm.comm a b)
  obtain ⟨s, hsS0, hsF, hs4⟩ := hA
  have hsR : s ∈ R := hS0le hsS0
  have hst : s ^ 2 = t := by
    have h2 : orderOf (s ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs4]; norm_num), hs4]
    exact hinv _ (R.pow_mem hsR 2) h2
  have htF : t ∈ F := hst ▸ F.pow_mem hsF 2
  refine ⟨htF, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxR : (x : G) ∈ R := (Subgroup.mem_subgroupOf.mp hx).1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRC hxR)
  · intro g hg n hn
    have hgC : (g : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hnR : (n : G) ∈ R := (Subgroup.mem_subgroupOf.mp hn).1
    have hnC : (n : G) ∈ Subgroup.centralizer ({t} : Set G) := hRC hnR
    have h1 := hRn.conj_mem ⟨n, hnC⟩ (Subgroup.mem_subgroupOf.mpr hnR) ⟨g, hgC⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨by simpa [Subgroup.mem_subgroupOf] using h1, (g * n * g⁻¹).2⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨htR, htF⟩
  · intro u hu hu2
    have hu2' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
    exact Subtype.ext (hinv _ (Subgroup.mem_subgroupOf.mp hu).1 hu2')
  · refine ⟨⟨s, hsF⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hsR, hsF⟩
    · rw [Subgroup.orderOf_mk]
      exact hs4

end CFSG.ClassicalInvolution.Nobq
