module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartI
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.LocalAnalysis.GLTheoremB.LayerTools
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

attribute [local instance] i116pI_act

@[expose] def i112Orbit {X : Type*} [Group X] (B L : Subgroup X) : Set (Subgroup X) :=
  {M | i116pI_Conj B L M}

section Orbit

variable {X : Type*} [Group X] {p : ℕ} {B L : Subgroup X}

theorem i112_conj_iff {M : Subgroup X} : i116pI_Conj B L M ↔ ∃ g ∈ B, M = GLBConj g L := by
  rw [← i116pI_mem_orbit_iff]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(b : X)⁻¹, B.inv_mem b.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g⁻¹, B.inv_mem hg⟩, by
      show GLBConj (g⁻¹)⁻¹ L = GLBConj g L
      rw [inv_inv]⟩

theorem mem_i112Orbit {M : Subgroup X} : M ∈ i112Orbit B L ↔ ∃ g ∈ B, M = GLBConj g L :=
  i112_conj_iff

theorem i112_self_mem_orbit : L ∈ i112Orbit B L :=
  mem_i112Orbit.2 ⟨1, B.one_mem, (gLBConj_one L).symm⟩

theorem i112_gLBConj_mem_orbit {g : X} (hg : g ∈ B) : GLBConj g L ∈ i112Orbit B L :=
  mem_i112Orbit.2 ⟨g, hg, rfl⟩

theorem i112_conj_eq_or_commute [Finite X] (hL : IsComponentOf L ⊤) {M N : Subgroup X}
    (hM : M ∈ i112Orbit B L) (hN : N ∈ i112Orbit B L) :
    M = N ∨ ∀ a ∈ M, ∀ b ∈ N, a * b = b * a :=
  CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (i116pI_isComponentOf_conj hL hM)
    (i116pI_isComponentOf_conj hL hN)

theorem i112_normalizer_inf_gLBConj (hB : IsElemAbelian p B) {g : X} (hg : g ∈ B) :
    Subgroup.normalizer (GLBConj g L : Set X) ⊓ B = Subgroup.normalizer (L : Set X) ⊓ B := by
  ext b
  rw [Subgroup.mem_inf, Subgroup.mem_inf, normalizer_gLBConj, mem_gLBConj]
  refine and_congr_left fun hb => ?_
  have : g * b * g⁻¹ = b := by
    rw [i116pI_comm hB hg hb]; group
  rw [this]

theorem i112_normalizer_inf_of_mem (hB : IsElemAbelian p B) {M : Subgroup X}
    (hM : M ∈ i112Orbit B L) :
    Subgroup.normalizer (M : Set X) ⊓ B = Subgroup.normalizer (L : Set X) ⊓ B := by
  obtain ⟨g, hg, rfl⟩ := mem_i112Orbit.1 hM
  exact i112_normalizer_inf_gLBConj hB hg

theorem i112_le_normalizer_iff (hB : IsElemAbelian p B) {M : Subgroup X}
    (hM : M ∈ i112Orbit B L) :
    B ≤ Subgroup.normalizer (M : Set X) ↔ B ≤ Subgroup.normalizer (L : Set X) := by
  have h := i112_normalizer_inf_of_mem hB hM
  rw [← inf_eq_right, ← inf_eq_right, h]

variable [Finite X]

theorem i112_relIndex_eq_pow (hp : p.Prime) (hB : IsElemAbelian p B)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    ∃ r : ℕ, 1 ≤ r ∧ (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r := by
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hB
  have hdvd : (Subgroup.normalizer (L : Set X)).relIndex B ∣ p ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨r, ?_, hr⟩
  by_contra h0
  have h0 : r = 0 := by omega
  rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hr
  exact hnL hr

omit [Finite X] in
theorem i112_ncard_orbit :
    (i112Orbit B L).ncard = (Subgroup.normalizer (L : Set X)).relIndex B := by
  have h : MulAction.orbit ↥B L = i112Orbit B L := by
    ext M; exact i116pI_mem_orbit_iff
  rw [← h, ← MulAction.index_stabilizer, i116pI_stabilizer_eq]
  rfl

theorem i112_finite_orbit : (i112Orbit B L).Finite := Set.toFinite _

omit [Finite X] in
theorem i112_natCard_orbit :
    Nat.card ↥(i112Orbit B L) = (Subgroup.normalizer (L : Set X)).relIndex B := by
  rw [← i112_ncard_orbit, Nat.card_coe_set_eq]

end Orbit

@[expose] def i112J {X : Type*} [Group X] (B L : Subgroup X) : Subgroup X :=
  ⨆ g ∈ B, GLBConj g L

section J

variable {X : Type*} [Group X] {p : ℕ} {B L : Subgroup X}

theorem i112_le_J {g : X} (hg : g ∈ B) : GLBConj g L ≤ i112J B L :=
  le_iSup₂_of_le g hg le_rfl

theorem i112_orbit_le_J {M : Subgroup X} (hM : M ∈ i112Orbit B L) : M ≤ i112J B L := by
  obtain ⟨g, hg, rfl⟩ := mem_i112Orbit.1 hM
  exact i112_le_J hg

theorem i112_J_le {K : Subgroup X} (h : ∀ M ∈ i112Orbit B L, M ≤ K) : i112J B L ≤ K :=
  iSup₂_le fun _ hg => h _ (i112_gLBConj_mem_orbit hg)

theorem i112_J_eq_iSup : i112J B L = ⨆ M : ↥(i112Orbit B L), (M : Subgroup X) :=
  le_antisymm (i112_J_le fun M hM => le_iSup (fun M : ↥(i112Orbit B L) => (M : Subgroup X)) ⟨M, hM⟩)
    (iSup_le fun M => i112_orbit_le_J M.2)

theorem i112_J_eq_iSup₂ : i112J B L = ⨆ M ∈ i112Orbit B L, M :=
  le_antisymm (i112_J_le fun M hM => le_iSup₂_of_le M hM le_rfl)
    (iSup₂_le fun _ hM => i112_orbit_le_J hM)

theorem i112_gLBConj_J_le {g : X} (hg : g ∈ B) : GLBConj g (i112J B L) ≤ i112J B L := by
  unfold i112J GLBConj
  rw [Subgroup.map_iSup]
  refine iSup_le fun g' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg' => ?_
  have := i112_le_J (L := L) (B.mul_mem hg' hg)
  rwa [← gLBConj_gLBConj] at this

theorem i112_B_le_normalizer_J : B ≤ Subgroup.normalizer (i112J B L : Set X) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (i112_gLBConj_J_le hg) ?_
  have := gLBConj_mono g (i112_gLBConj_J_le (L := L) (B.inv_mem hg))
  rwa [gLBConj_gLBConj_inv] at this

end J

section Sub

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

omit [Finite X] in
theorem i112_isComponentOf_of_mem {M : Subgroup X} (hL : IsComponentOf L ⊤)
    (hM : M ∈ i112Orbit B L) : IsComponentOf M ⊤ :=
  i116pI_isComponentOf_conj hL (i112_conj_iff.2 (mem_i112Orbit.1 hM))

theorem i112_isSubnormal_J (hL : IsComponentOf L ⊤) : IsSubnormal (i112J B L) ⊤ := by
  rw [i112_J_eq_iSup₂]
  exact isSubnormal_iSup_components _ fun M hM => i112_isComponentOf_of_mem hL hM

omit [Finite X] in
theorem i112_isQuasisimple_of_mem {M : Subgroup X} (hL : IsComponentOf L ⊤)
    (hM : M ∈ i112Orbit B L) : CFSG.Open.IsQuasisimple ↥M :=
  (i112_isComponentOf_of_mem hL hM).2.2

omit [Finite X] in
theorem i112_equiv_of_mem {M : Subgroup X} (hM : M ∈ i112Orbit B L) : Nonempty (↥L ≃* ↥M) := by
  obtain ⟨g, -, rfl⟩ := mem_i112Orbit.1 hM
  exact ⟨conjEquiv g L⟩

theorem i112_isPGroup_inf_centralizer (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    {N : Subgroup X} (hN : IsSubnormal N ⊤) :
    IsPGroup p ↥(N ⊓ Subgroup.centralizer (N : Set X)) := by
  have := Fact.mk hp
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg
  obtain ⟨hgN, hgC⟩ := hg
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe]
  show orderOf g = p ^ k
  set q := g ^ (p ^ k) with hqdef
  have hq : orderOf q = m := by
    rw [hqdef, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hUN : Subgroup.zpowers q ≤ N := Subgroup.zpowers_le.2 (N.pow_mem hgN _)
  have hcen : ∀ n ∈ N, ∀ j ∈ Subgroup.zpowers q, n * j = j * n := by
    intro n hn j hj
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj
    exact ((Commute.pow_right (hgC n hn) (p ^ k)).zpow_right z).eq
  have hnorm : ((Subgroup.zpowers q).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).2
      fun n hn => i116pI_mem_normalizer_of_commute (hcen n hn)
  have hsub : IsSubnormal (Subgroup.zpowers q) ⊤ :=
    isSubnormal_trans' (IsSubnormal.step hUN hnorm (IsSubnormal.refl N)) hN
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers q)) := by
    rw [Nat.card_zpowers, hq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h1 : Subgroup.zpowers q ≤ GLAPPrimeCoreOf p (⊤ : Subgroup X) := by
    calc Subgroup.zpowers q = GLAPPrimeCoreOf p (Subgroup.zpowers q) :=
          (glaPPrimeCoreOf_eq_self_of_coprime hcop).symm
      _ ≤ _ := glaPPrimeCoreOf_le_of_isSubnormal hp hsub
  rw [glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO, le_bot_iff, Subgroup.zpowers_eq_bot] at h1
  have hm1 : m = 1 := by rw [← hq, h1, orderOf_one]
  rw [hord, hm1, mul_one]

theorem i112_isPGroup_center_orbit (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    (hL : IsComponentOf L ⊤) {M : Subgroup X} (hM : M ∈ i112Orbit B L) :
    IsPGroup p ↥(M ⊓ Subgroup.centralizer (M : Set X)) :=
  i112_isPGroup_inf_centralizer hp hO (i112_isComponentOf_of_mem hL hM).2.1

theorem i112_isPGroup_center_J (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    (hL : IsComponentOf L ⊤) :
    IsPGroup p ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) :=
  i112_isPGroup_inf_centralizer hp hO (i112_isSubnormal_J hL)

@[expose] def i112Fam (B L : Subgroup X) : ↥(i112Orbit B L) → Subgroup X := fun M => M

theorem i112_pairwise_commute (hL : IsComponentOf L ⊤) :
    Pairwise fun i j : ↥(i112Orbit B L) => ∀ x y : X, x ∈ i112Fam B L i → y ∈ i112Fam B L j →
      Commute x y := by
  intro i j hij x y hx hy
  rcases i112_conj_eq_or_commute hL i.2 j.2 with h | h
  · exact absurd (Subtype.ext h) hij
  · exact h x hx y hy

omit [Finite X] in
theorem i112_iSup_fam : ⨆ i, i112Fam B L i = i112J B L :=
  (i112_J_eq_iSup (B := B) (L := L)).symm

instance : Finite ↥(i112Orbit B L) := (i112_finite_orbit (B := B) (L := L)).to_subtype

theorem i112_card_fam (hp : p.Prime) (hB : IsElemAbelian p B)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    ∃ r : ℕ, 1 ≤ r ∧ Nat.card ↥(i112Orbit B L) = p ^ r := by
  obtain ⟨r, hr, h⟩ := i112_relIndex_eq_pow hp hB hnL
  exact ⟨r, hr, by rw [i112_natCard_orbit, h]⟩

end Sub

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
