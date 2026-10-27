module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Uni
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinusTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankBasic

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.RankThreeTheoremC
open scoped Pointwise

section Blocks

variable {f t s ε : ℕ} {K : Type} [Field K]

private theorem uniBlock_cases_of_sixty (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t) (j : Option ↥I)
    (hq : CFSG.Open.IsQuasisimple (LeviBlock.uniBlockSub (s := s) (ε := ε) h I j))
    (h60 : Nat.card (↥(LeviBlock.uniBlockSub (s := s) (ε := ε) h I j) ⧸
      Subgroup.center ↥(LeviBlock.uniBlockSub (s := s) (ε := ε) h I j)) = 60) :
    (j = none ∧ f = 2 ∧ s = 1 ∧ ε = 0) ∨
      ∃ b : ↥I, j = some b ∧ f = 1 ∧ b.1 - LeviBlock.predCut I b.1 = 2 := by
  rw [(LeviBlock.uniBlockSub_facts h hε hI j).2 hq] at h60
  rcases j with _ | b
  · change ordTwistedA (2 * s + ε - 1) (2 ^ f) = 60 at h60
    obtain ⟨hn, h4⟩ := (ordTwistedA_eq_sixty_iff (f := f) rfl).mp h60
    exact Or.inl ⟨rfl, Nat.pow_right_injective le_rfl (h4.trans (by norm_num)), by omega,
      by omega⟩
  · change ordA (b.1 - LeviBlock.predCut I b.1 - 1) ((2 ^ f) ^ 2) = 60 at h60
    obtain ⟨h1, h4⟩ := (ordA_eq_sixty_iff (f := 2 * f) (by rw [← pow_mul, mul_comm])).mp h60
    have h2 : 2 ^ f = 2 := Nat.pow_left_injective two_ne_zero (h4.trans (by norm_num))
    have := LeviBlock.predCut_lt (I := I) (hI.le b.1 b.2).1
    exact Or.inr ⟨b, rfl, Nat.pow_right_injective le_rfl (h2.trans (by norm_num)), by omega⟩

private theorem four_le_of_two_gaps {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t) {b b' : ↥I}
    (hne : b ≠ b') (hb : b.1 - LeviBlock.predCut I b.1 = 2)
    (hb' : b'.1 - LeviBlock.predCut I b'.1 = 2) : 4 ≤ t := by
  have ht := (hI.le b.1 b.2).2
  have ht' := (hI.le b'.1 b'.2).2
  rcases lt_or_gt_of_ne (fun h => hne (Subtype.ext h) : b.1 ≠ b'.1) with h | h
  · have := LeviBlock.le_predCut b.2 h
    omega
  · have := LeviBlock.le_predCut b'.2 h
    omega

private theorem uni_blocks_of_fiveComponents (hLB : LeviBlocksOfFiveComponents) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) (h : UnitaryFieldData 2 f K)
    (hε : ε ≤ 1) {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t) (ρ : hypSU h (t + s) ε →* ↥L)
    (hρ : Function.Surjective ρ)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) (g : hypSU h (t + s) ε)
    (hJ : ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i) :
    (∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C →
      (f = 2 ∧ s = 1 ∧ ε = 0) ∨ (f = 1 ∧ 2 ≤ t)) ∧
    ∀ C₁ C₂ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), C₁ ≠ C₂ → IsFiveComponent P C₁ →
      IsFiveComponent P C₂ → f = 1 ∧ 4 ≤ t := by
  have : Finite K := h.finite
  set β := LeviBlock.uniLeviHom (s := s) h hε hI
  set e' := LeviBlock.stabMulEquiv g hJ
  have hrange : (β.comp e'.toMonoidHom).range = β.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map (e'.toMonoidHom),
      Subgroup.map_top_of_surjective _ e'.surjective, ← MonoidHom.range_eq_map]
  have hker : ρ.ker ≤ Subgroup.center (hypSU h (t + s) ε) := fun y hy =>
    normOneScalars_le_center h (hypSU h (t + s) ε) (2 * (t + s) + ε)
      ((hZ y).1 (by rw [MonoidHom.mem_ker.1 hy]; exact Subgroup.one_mem _))
  obtain ⟨h₁, h₂⟩ := hLB Y L P hPL _ ρ hρ hker (Option ↥I) (LeviBlock.uniBlockGroup K s ε I)
    (LeviBlock.uniBlockSub (s := s) (ε := ε) h I) (β.comp e'.toMonoidHom)
    ((LeviBlock.isPGroup_ker_uniLeviHom h hε hI).comap_of_injective e'.toMonoidHom e'.injective)
    (hrange ▸ LeviBlock.pi_uniBlockSub_le_range h hε hI)
    (hrange ▸ LeviBlock.commutator_range_le_pi h hε hI)
    (fun j => (LeviBlock.uniBlockSub_facts h hε hI j).1)
  refine ⟨fun C hC => ?_, fun C₁ C₂ hne hC₁ hC₂ => ?_⟩
  · obtain ⟨j, hq, h60⟩ := h₁ C hC
    rcases uniBlock_cases_of_sixty h hε hI j hq h60 with ⟨-, hf, hs, hε0⟩ | ⟨b, -, hf, hb⟩
    · exact Or.inl ⟨hf, hs, hε0⟩
    · have := (hI.le b.1 b.2).2
      exact Or.inr ⟨hf, by omega⟩
  · obtain ⟨j₁, j₂, hj, hq₁, hq₂, h60₁, h60₂⟩ := h₂ C₁ C₂ hne hC₁ hC₂
    rcases uniBlock_cases_of_sixty h hε hI j₁ hq₁ h60₁ with ⟨rfl, hf, -⟩ | ⟨b₁, rfl, hf, hb₁⟩ <;>
      rcases uniBlock_cases_of_sixty h hε hI j₂ hq₂ h60₂ with ⟨rfl, hf', -⟩ | ⟨b₂, rfl, hf', hb₂⟩
    · exact absurd rfl hj
    · exfalso
      omega
    · exfalso
      omega
    · exact ⟨hf, four_le_of_two_gaps hI (fun he => hj (by rw [he])) hb₁ hb₂⟩

end Blocks

section Torus

variable {K : Type} [Field K]

private theorem pow_three_eq_one_of_card_four (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hU : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← hU]
  exact pow_card_eq_one'

private noncomputable def diagTorus (hK : Nat.card K = 4) (k : ℕ) {n : ℕ} (hn : k + 1 ≤ n) :
    (Fin k → Kˣ) →* StatedSU n 2 K :=
  MonoidHom.mk' (fun c => ⟨WeakClosureHeis.diagGL n (KFactProofs.minusTorusVec k c),
      KFactProofs.heisU_diagGL_mem_statedSU two_ne_zero _
        (fun _ => pow_three_eq_one_of_card_four hK _) (KFactProofs.prod_minusTorusVec hn c)⟩)
    fun c c' => Subtype.ext (by
      change WeakClosureHeis.diagGL n (KFactProofs.minusTorusVec k (c * c')) =
        WeakClosureHeis.diagGL n (KFactProofs.minusTorusVec k c) *
          WeakClosureHeis.diagGL n (KFactProofs.minusTorusVec k c')
      rw [KFactProofs.minusTorusVec_mul, map_mul])

private theorem eq_one_of_diagTorus_mem_scalars (hK : Nat.card K = 4) {k n : ℕ} (hn : k + 2 ≤ n)
    {c : Fin k → Kˣ}
    (hc : ((diagTorus hK k (n := n) (by omega) c : StatedSU n 2 K) : GL (Fin n) K) ∈
      StatedScalars (Fin n) K) : c = 1 := by
  obtain ⟨u, hu⟩ := KFactProofs.heisU_diagGL_mem_scalars hc
  have hu1 : u = 1 := by
    have e := hu ⟨k + 1, by omega⟩
    have h1 : ¬ k + 1 < k := by omega
    have h2 : k + 1 ≠ k := by omega
    simp only [KFactProofs.minusTorusVec, h1, h2, ↓reduceDIte, ↓reduceIte] at e
    exact e.symm
  funext j
  have e := hu ⟨j, by omega⟩
  simp only [KFactProofs.minusTorusVec, j.isLt, ↓reduceDIte, Fin.eta] at e
  rw [e, hu1, Pi.one_apply]

private theorem eq_one_of_diagTorus_mem_centralizer {Y : Type} [Group Y] {L : Subgroup Y}
    (hK : Nat.card K = 4) {k n : ℕ} (hn : k + 2 ≤ n) (ρ : StatedSU n 2 K →* ↥L)
    (hZ : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K)
    (c : Fin k → Kˣ)
    (hc : (L.subtype.comp (ρ.comp (diagTorus hK k (by omega)))) c ∈
      Subgroup.centralizer (L : Set Y)) : c = 1 := by
  refine eq_one_of_diagTorus_mem_scalars hK hn ((hZ _).1 ?_)
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc l l.2)

end Torus

private theorem e9_of_torus {Y : Type} [Group Y] {L : Subgroup Y} {M : Type*} [CommGroup M]
    (hM : Nat.card M = 3) (φ : (Fin 2 → M) →* Y) (hL : φ.range ≤ L)
    (hc : ∀ a, φ a ∈ Subgroup.centralizer (L : Set Y) → a = 1) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    exact fun a ha => hc a (by rw [ha]; exact Subgroup.one_mem _)
  have hpow : ∀ a : Fin 2 → M, a ^ 3 = 1 := fun a => by
    funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hM]
    exact pow_card_eq_one'
  refine ⟨φ.range, hL, KFactProofs.isElemAbelian_range_of_pow (fun a b => mul_comm a b) hpow φ,
    ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, hM, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    rw [hc a hxC, map_one]
    exact Subgroup.one_mem _

section MuThree

variable {K : Type} [Field K]

private theorem bar_eq_of_pow_three (h : UnitaryFieldData 2 2 K) {x : Kˣ} (hx : x ^ 3 = 1) :
    h.bar (x : K) = x := by
  have h3 : (x : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  rw [UnitaryFieldData.bar_apply]
  calc (x : K) ^ 2 ^ 2 = (x : K) ^ 3 * x := by ring
    _ = (x : K) := by rw [h3, one_mul]

private theorem exists_threeSubgroup (hK : Nat.card K = 16) :
    ∃ μ : Subgroup Kˣ, Nat.card μ = 3 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hU : Nat.card Kˣ = 15 := by rw [Nat.card_units, hK]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hU]; norm_num)
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

private theorem pow_three_of_mem {μ : Subgroup Kˣ} (hμ : Nat.card μ = 3) {x : Kˣ} (hx : x ∈ μ) :
    x ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.1 (hμ ▸ Subgroup.orderOf_dvd_natCard μ hx)

private theorem eq_one_of_sq_of_mem {μ : Subgroup Kˣ} (hμ : Nat.card μ = 3) {x : Kˣ}
    (hx : x ∈ μ) (hx2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := hμ ▸ Subgroup.orderOf_dvd_natCard μ hx
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h3 : orderOf x ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h3))

end MuThree

private theorem exists_statedSU_cover {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f n : ℕ) (ρ : StatedSU n (2 ^ f) K →* ↥L),
      Nat.card K = (2 ^ f) ^ 2 ∧
      (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f ∧ r₀ + 1 = n) ∧ Function.Surjective ρ ∧
      ∀ g, ρ g ∈ Subgroup.center ↥L ↔ (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r₀ q =>
    change q.p = 2 at hd
    have hc := SQTK.statedClassicalModel_twistedA r₀ q hv e
    rw [hd] at hc
    obtain ⟨⟨-, -, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
    obtain ⟨ρ, hρ, -, hρe⟩ := kFactCoverUnitary Y L hL hodd _ _ K hcard hn3 hnq e'
    refine ⟨K, hK, hKfin, q.exponent, r₀ + 1, ρ, hcard, fun r₁ q₁ h₁ => ?_, hρ, fun g => ?_⟩
    · injection h₁ with h₂ h₃
      exact ⟨by rw [← h₃, hqc], by rw [h₂]⟩
    · rw [← QuotientGroup.eq_one_iff, ← e'.map_eq_one_iff, hρe, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
  | _ => exact hd.elim

private theorem statedSU_eq_of_index {d : TauCeti.ValidLieTypeIndex} (hd : IdxTwistedA d.1)
    {f f' t s ε n : ℕ}
    (hq : ∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f ∧ r₀ + 1 = 2 * (t + s) + ε)
    (hq' : ∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f' ∧ r₀ + 1 = n) :
    f' = f ∧ n = 2 * (t + s) + ε := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r₀ q =>
    obtain ⟨h₁, h₂⟩ := hq r₀ q rfl
    obtain ⟨h₁', h₂'⟩ := hq' r₀ q rfl
    exact ⟨Nat.pow_right_injective le_rfl (h₁'.symm.trans h₁), by omega⟩
  | _ => exact hd.elim

theorem kFactCompParabTwoFivesOn_twistedA (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabTwoFivesOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC h3 C₁ C₂ hne hC₁ hC₂
  exfalso
  obtain ⟨d, hdA, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hdA e
  obtain ⟨hf, ht⟩ :=
    (uni_blocks_of_fiveComponents hLB hCP.parab.1 h hε hI ρ hρ hZ g hJ).2 C₁ C₂ hne hC₁ hC₂
  obtain ⟨K', _, _, f', n, ρ', hK', hq', -, hZ'⟩ := exists_statedSU_cover hCP.comp hCP.odd d hdA e
  obtain ⟨rfl, hn⟩ := statedSU_eq_of_index hdA hq hq'
  subst hf
  have hK4 : Nat.card K' = 4 := by rw [hK']; norm_num
  have h4 : 4 ≤ CFSG.Open.pRank 3 L := by
    have hc := eq_one_of_diagTorus_mem_centralizer hK4 (k := 4) (by omega) ρ' hZ'
    refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
      (fun a => ?_) ?_ (L.subtype.comp (ρ'.comp (diagTorus hK4 4 (n := n) (by omega)))) ?_ ?_
    · funext j
      rw [Pi.pow_apply, Pi.one_apply]
      exact pow_three_eq_one_of_card_four hK4 (a j)
    · rw [Nat.card_fun, Nat.card_units, hK4, Nat.card_fin]
    · rw [injective_iff_map_eq_one]
      exact fun c hc1 => hc c (by rw [hc1]; exact Subgroup.one_mem _)
    · rintro _ ⟨c, rfl⟩
      exact (ρ' _).2
  omega

theorem kFactCompParabOneFiveOn_twistedA (hLB : LeviBlocksOfFiveComponents) :
    KFactCompParabOneFiveOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC C hC5
  refine Or.inl ?_
  obtain ⟨d, hdA, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hdA e
  rcases (uni_blocks_of_fiveComponents hLB hCP.parab.1 h hε hI ρ hρ hZ g hJ).1 C hC5 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, ht⟩
  ·
    obtain ⟨μ, hμ⟩ := exists_threeSubgroup (K := K) (by rw [h.card]; norm_num)
    have hA : ∀ x ∈ μ, h.bar (x : K) = x := fun x hx =>
      bar_eq_of_pow_three h (pow_three_of_mem hμ hx)
    have hodd : ∀ x ∈ μ, x ^ 2 = 1 → x = 1 := fun x hx hx2 => eq_one_of_sq_of_mem hμ hx hx2
    have hr : 2 ≤ t + 1 := by
      have := (hI.le t hI.mem).1
      omega
    set φ₀ := KFactProofs.uniTorusFix h hA (t + 1) 0 2
    refine e9_of_torus hμ (L.subtype.comp (ρ.comp φ₀)) ?_ fun a ha => ?_
    · rintro _ ⟨a, rfl⟩
      exact (ρ (φ₀ a)).2
    · refine KFactProofs.uniEq_one_of_torusFix_mem_hypScalars h hA hodd hr ((hZ _).1 ?_)
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp ha l l.2)
  ·
    obtain ⟨K', _, _, f', n, ρ', hK', hq', -, hZ'⟩ :=
      exists_statedSU_cover hCP.comp hCP.odd d hdA e
    obtain ⟨rfl, hn⟩ := statedSU_eq_of_index hdA hq hq'
    have hK4 : Nat.card K' = 4 := by rw [hK']; norm_num
    refine e9_of_torus (M := K'ˣ) (by rw [Nat.card_units, hK4])
      (L.subtype.comp (ρ'.comp (diagTorus hK4 2 (n := n) (by omega)))) ?_
      (eq_one_of_diagTorus_mem_centralizer hK4 (by omega) ρ' hZ')
    rintro _ ⟨c, rfl⟩
    exact (ρ' _).2

end CFSG.AGLEmbedding
