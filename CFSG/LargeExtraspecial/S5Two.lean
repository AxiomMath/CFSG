module

public import CFSG.LargeExtraspecial.S5Diag
public import CFSG.LargeExtraspecial.S5Odd
public import CFSG.LargeExtraspecial.S5Fac
public import CFSG.LargeExtraspecial.S5Q
public import CFSG.LargeExtraspecial.S5R
public import CFSG.LargeExtraspecial.S5Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem IsSylowTwoIn.subgroupOf_top {X : Type*} [Group X] {P Z : Subgroup X}
    (h : IsSylowTwoIn P Z) : IsSylowTwoIn (P.subgroupOf Z) (⊤ : Subgroup Z) := by
  refine ⟨le_top, h.isPGroup.of_equiv (subgroupOfEquivOfLe h.le).symm, ?_⟩
  rw [relIndex_top_right]
  exact h.not_dvd

theorem IsSylowTwoIn.subgroupOf {X : Type*} [Group X] {P Y R : Subgroup X}
    (h : IsSylowTwoIn P Y) (hYR : Y ≤ R) : IsSylowTwoIn (P.subgroupOf R) (Y.subgroupOf R) := by
  refine ⟨fun x hx => h.le hx,
    h.isPGroup.of_equiv (subgroupOfEquivOfLe (h.le.trans hYR)).symm, ?_⟩
  rw [relIndex_subgroupOf hYR]
  exact h.not_dvd

namespace SwapData

variable (D : SwapData S g)

theorem t_ne_one : D.t ≠ 1 := by
  intro h
  apply D.ne
  rw [h]
  ext x
  simp

theorem Xhat_le_Rbar (H : Hyp4 S g) {s : S.O} (hsZ : s ∈ D.Z) (hs1 : s ≠ 1) {k : ℕ}
    (hks : s ^ (2 ^ k) = 1) (hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g) : D.Xhat ≤ Rbar S g D.t := by
  set N' := ((Rbar S g D.t).comap D.chi).map D.Z.subtype with hN'
  have hN'Z : N' ≤ D.Z := map_subtype_le _
  have hmemN' : ∀ z : D.Z, (z : S.O) ∈ N' ↔ D.chi z ∈ Rbar S g D.t := by
    intro z
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [show z = w from Subtype.ext hwz.symm]
      exact hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hnorm : ∀ a ∈ D.Z, ∀ n ∈ N', a * n * a⁻¹ ∈ N' := by
    intro a ha n hn
    have hnZ := hN'Z hn
    have e : a * n * a⁻¹ = ((⟨a, ha⟩ * ⟨n, hnZ⟩ * (⟨a, ha⟩ : D.Z)⁻¹ : D.Z) : S.O) := rfl
    rw [e, hmemN', map_mul, map_mul, map_inv]
    have hn' := (hmemN' ⟨n, hnZ⟩).mp hn
    have haX := D.chi_mem_Xhat ⟨a, ha⟩
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (D.Xhat_le_Mbar haX)
    have hkt : S.ρ k * D.t = D.t * S.ρ k := by
      rw [hk]
      exact mem_centralizer_singleton_iff.mp (D.Xhat_le_centralizer H haX)
    have := conj_mem_Rbar hkt hn'
    rwa [hk] at this
  rcases commute_or_eq_of_normalized D.isQuasisimple_Z hN'Z hnorm with hcen | heq
  · exfalso
    have hsN : s ∈ N' := (hmemN' ⟨s, hsZ⟩).mpr (Lbar_le_Rbar D.mem_Lbar hsL)
    exact hs1 (eq_one_of_mem_center_of_pow S D.isComponentOf.2.1 hsZ (hcen s hsN) hks)
  · rintro _ ⟨z, rfl⟩
    exact (hmemN' z).mp (by rw [heq]; exact z.2)

theorem isSolvable_of_le_Lbar (H : Hyp4 S g) {A : Subgroup S.O} (hA : A ≤ S.Lbar g) :
    Group.IsSolvable A :=
  Group.isSolvable_of_comm fun a b => Subtype.ext (S4.Lbar_comm S H.conj_mem (hA a.2) (hA b.2))

theorem not_Xhat_le_Nbar (H : Hyp4 S g) {s : S.O} (hsZ : s ∈ D.Z) (hs1 : s ≠ 1) {k : ℕ}
    (hks : s ^ (2 ^ k) = 1) (hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g) :
    ¬ D.Xhat ≤ Nbar S g D.t := by
  intro h
  have haQ := H.conj_mem
  have hXq := D.isQuasisimple_Xhat
  have hnormL : ∀ y ∈ D.Xhat, y ∈ normalizer (S.Lbar g : Set S.O) := fun y hy =>
    Nbar_le_normalizer haQ H.conj_ne (Lbar_mem_Dset D.mem_Lbar) (h hy)
  have hnorm : ∀ a ∈ D.Xhat, ∀ n ∈ D.Xhat ⊓ S.Lbar g, a * n * a⁻¹ ∈ D.Xhat ⊓ S.Lbar g :=
    fun a ha n hn => ⟨D.Xhat.mul_mem (D.Xhat.mul_mem ha hn.1) (D.Xhat.inv_mem ha),
      (mem_normalizer_iff.mp (hnormL a ha) n).mp hn.2⟩
  rcases commute_or_eq_of_normalized hXq inf_le_left hnorm with hcen | heq
  · have hcX : D.chi ⟨s, hsZ⟩ ∈ D.Xhat ⊓ S.Lbar g := ⟨D.chi_mem_Xhat _, hsL⟩
    have hc1 : D.chi ⟨s, hsZ⟩ = 1 := by
      refine D.eq_one_of_mem_center_Xhat (D.chi_mem_Xhat _) (hcen _ hcX) (k := k) ?_
      rw [← map_pow]
      have : (⟨s, hsZ⟩ : D.Z) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hks)
      rw [this, map_one]
    rw [chi_apply] at hc1
    have hsW : s ∈ D.W := by
      have e : s = (D.t * s * D.t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hc1
      rw [e]
      exact D.W.inv_mem (D.conj_mem_W hsZ)
    exact hs1 (eq_one_of_mem_center_of_pow S D.isComponentOf.2.1 hsZ
      (fun y hy => D.mul_comm_of_mem_W hsW hy) hks)
  · have hXL : D.Xhat ≤ S.Lbar g := by rw [← heq]; exact inf_le_right
    exact not_isSolvable_of_isQuasisimple hXq (isSolvable_of_le_Lbar H hXL)

include D in
theorem false (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C)
    (hn : 4 < S.width) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  have htL := D.mem_Lbar
  have ht1 := D.t_ne_one
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge (S.Lbar_le_Mbar g) (S4.isPGroup_Lbar S haQ)
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup hT.le hLT
  have hP := hT.inf_of_isSubnormal D.isComponentOf.2.1
  have hPne := hP.ne_bot (two_dvd_card_of_isQuasisimple D.isQuasisimple_Z)
  obtain ⟨⟨s, hsP⟩, hs1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPne
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hsZ : s ∈ D.Z := hsP.2
  obtain ⟨ks, hks⟩ := hP.exists_pow_eq_one hsP
  have hPL : ∀ x (hx : x ∈ T ⊓ D.Z), D.chi ⟨x, hx.2⟩ ∈ S.Lbar g := fun x hx => by
    obtain ⟨k, hk⟩ := hP.exists_pow_eq_one hx
    exact D.chi_mem_Lbar H ⟨x, hx.2⟩ (hTN hx.1) hk
  have hsL : D.chi ⟨s, hsZ⟩ ∈ S.Lbar g := hPL s hsP
  set B := ((T ⊓ D.Z).subgroupOf D.Z).map D.chi with hB
  have hBL : B ≤ S.Lbar g := by
    rintro _ ⟨⟨x, hxZ⟩, hx, rfl⟩
    exact hPL x (mem_subgroupOf.mp hx)
  have hBX : IsSylowTwoIn B D.Xhat := by
    have := hP.subgroupOf_top.map D.chi
    rwa [← MonoidHom.range_eq_map] at this
  have hXR := D.Xhat_le_Rbar H hsZ hs1 hks hsL
  have hXq := D.isQuasisimple_Xhat
  have hXN := D.not_Xhat_le_Nbar H hsZ hs1 hks hsL
  have hRL : Rbar S g D.t ≠ S.Lbar g := fun h =>
    not_isSolvable_of_isQuasisimple hXq (isSolvable_of_le_Lbar H (h ▸ hXR))
  have hXsubR : IsSubnormal D.Xhat (Rbar S g D.t) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le (D.isSubnormal_Xhat H) hXR
      (le_inf Rbar_le_Mbar (Rbar_le_centralizer haQ))
  obtain ⟨⟨hfac, -⟩, -, h3⟩ := Q.quasisimple hNo htL ht1 hRL
    (isSubnormal_imgR haQ hXR hXsubR) (isQuasisimple_imgR haQ hXR hXq hXN)
  have hBXR := (hBX.subgroupOf hXR).map (resV haQ D.t)
  obtain ⟨hVQ, h4⟩ := h3 ⟨imgR haQ D.t B, hBXR.le, hBXR.isPGroup, hBXR.not_dvd, by
    rintro _ ⟨b1, hb1, rfl⟩ _ ⟨b2, hb2, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (S4.Lbar_comm S haQ (hBL (mem_subgroupOf.mp hb1))
      (hBL (mem_subgroupOf.mp hb2)))⟩
  have hLN : ∀ τ ∈ S.Lbar g ⊓ Nbar S g D.t, τ = 1 ∨ τ = D.t := by
    intro τ hτ
    refine eq_one_or_eq_of_factor H C htL ht1 hVQ hfac hτ.1 fun y hy => ?_
    exact commute_of_mem_Lbar_inf_Nbar H htL hXR hXq hXN
      (fun s' hs' y' hy' => D.conj_mem_Xhat H hsZ hs1 hks hsL hs' hy')
      (fun z hz hc k hk => D.eq_one_of_mem_center_Xhat hz hc hk) hτ.1 hτ.2 hy
  have hcard := card_Lbar_eq haQ htL
  have h2 := card_le_two_of_subset hLN
  have h16 := sixteen_le_card_Lbar C hn
  have h8 : Nat.card (S.Lbar g) ≤ 8 := by
    rw [hcard]
    calc Nat.card (S.Lbar g ⊓ Nbar S g D.t : Subgroup S.O) * Nat.card (LmodN S g D.t)
        ≤ 2 * 4 := Nat.mul_le_mul h2 h4
      _ = 8 := by norm_num
  omega

end SwapData

end CFSG.LargeExtraspecial.S5
