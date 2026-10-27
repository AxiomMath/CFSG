module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs

variable {G : Type} [Group G] [Finite G]

theorem l3gl_branchB_data (h191 : Lemma54Ns.Input19_1_2) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {L : Subgroup G} (hcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L) :
    ∃ Dt Ht : Subgroup (MulAut (barOf 3 L)), IsEkIn 3 2 ⊤ Dt ∧ innerAut (barOf 3 L) ≤ Ht ∧
      localDeltaIn 3 Ht Dt ≠ ⊥ ∧ Dt ≤ autBar 3 B L := by
  have := hS.simple
  obtain ⟨hDB, hDel, hDcard⟩ := hD
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set X : Subgroup G := GLADelta 3 D ⊓ C with hXdef
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hDB hd) hb
  obtain ⟨hnorm, hmain⟩ :=
    h191 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hDne b hbD hb1 (hBel.2 b hb)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hnorm L hcomp
  have hnot' : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    apply hnot
    have hLX : ⁅L, X⁆ ≤ L := Subgroup.commutator_le.2 fun ℓ hℓ x hx => by
      rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) ℓ⁻¹).1 (L.inv_mem hℓ)
      have h2 := L.mul_mem hℓ h1
      simpa [mul_assoc] using h2
    intro y hy
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three C L ⟨hle hy, hLX hy⟩
    rwa [inf_eq_right.2 hcomp.1] at h3
  obtain ⟨hker, hDN, himg⟩ := hmain L hcomp hnot'
  set Dt : Subgroup (MulAut (barOf 3 L)) :=
    (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hDt
  set Ht : Subgroup (MulAut (barOf 3 L)) :=
    ((X ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hHt
  have hDcard9 : Nat.card ↥Dt = 9 := by
    rw [hDt, Lemma54Ns.card_map_barAut_of_kerB_eq_bot hDN hker, hDcard]
    norm_num
  have hDtE : IsEkIn 3 2 ⊤ Dt :=
    ⟨le_top, isElemAbelian_map (isElemAbelian_subgroupOf hDel) _, by rw [hDcard9]; norm_num⟩
  have hinn : innerAut (barOf 3 L) ≤ Ht :=
    Lemma54Ns.innerAut_le_map (p := 3) (le_sup_right : L ≤ X ⊔ L)
  have hdelta : localDeltaIn 3 Ht Dt ≠ ⊥ := by
    intro hbot
    rw [hbot] at himg
    exact Lemma54Ns.map_barAut_ne_bot hXN hnot (le_bot_iff.1 himg)
  have hDtB : Dt ≤ autBar 3 B L := Subgroup.map_mono (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hDB hx, x.2⟩)
  exact ⟨Dt, Ht, hDtE, hinn, hdelta, hDtB⟩

omit [Finite G] in
theorem l3gl_autBar_comm {B : Subgroup G} (hBel : IsElemAbelian 3 B) (L : Subgroup G) :
    ∀ β ∈ autBar 3 B L, ∀ γ ∈ autBar 3 B L, β * γ = γ * β := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact elemAbelian_comm hBel (Subgroup.mem_subgroupOf.1 hx).1 (Subgroup.mem_subgroupOf.1 hy).1

omit [Finite G] in
theorem l3gl_conj_mem_autBar {B L : Subgroup G} {y : G} (hy : y ∈ L) (hyB : y ∈ B) :
    MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : barOf 3 L) ∈ autBar 3 B L := by
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy
  refine ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 ⟨hyB, hyN⟩, ?_⟩
  exact (rho_of_mem hyN).symm.trans (rho_of_mem_L hy)

theorem l3gl_mk_ne_one {B L : Subgroup G} (hBel : IsElemAbelian 3 B) {y : G} (hy : y ∈ L)
    (hyB : y ∈ B) (hy1 : y ≠ 1) : (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : barOf 3 L) ≠ 1 := by
  intro h1
  have hmem : (⟨y, hy⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 h1
  set x : GLAPPrimeCore 3 ↥L := ⟨⟨y, hy⟩, hmem⟩ with hx
  have hx3 : x ^ 3 = 1 := Subtype.ext (Subtype.ext (hBel.2 y hyB))
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hcop := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
    Nat.prime_three ↥L
  have h2 : Nat.Coprime (orderOf x) (Nat.card (GLAPPrimeCore 3 ↥L)) :=
    Nat.Coprime.coprime_dvd_left hdvd hcop
  have h3 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd h2 (orderOf_dvd_natCard x)
  have h4 : x = 1 := orderOf_eq_one_iff.1 h3
  exact hy1 (congrArg (fun z : GLAPPrimeCore 3 ↥L => ((z : ↥L) : G)) h4)

theorem l3gl_hasOrderThreeLift_branchB (h191 : Lemma54Ns.Input19_1_2) {m : ℕ}
    (hS : GLStanding G m 3) {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G}
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hty : IsExtremalType (barOf 3 L)) {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L)
    {y : G} (hy : y ∈ L) (hyB : y ∈ B) (hy1 : y ≠ 1) :
    HasOrderThreeLift (barOf 3 L) (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) := by
  obtain ⟨Dt, Ht, hDt, hinn, hdelta, hDtB⟩ := l3gl_branchB_data h191 hS hBel hb hb1 hcomp hD hnot
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hcomp
  refine hasOrderThreeLift_of_localDeltaIn_ne_bot hq hty hDt hinn hdelta _
    (l3gl_mk_ne_one hBel hy hyB hy1) fun d hd => ?_
  exact l3gl_autBar_comm hBel L d (hDtB hd) _ (l3gl_conj_mem_autBar hy hyB)

end CFSG.HardMathSupport.Solomon.Coordinator
