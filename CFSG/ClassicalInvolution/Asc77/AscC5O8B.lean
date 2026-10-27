module

public import CFSG.ClassicalInvolution.Asc77.AscC5O1C

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

@[expose] noncomputable def quotAutHom {H : Type} [Group H] (J L₀ : Subgroup G)
    (hL : ∀ g ∈ L₀, conjSub g J = J) (e : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* H) :
    ↥L₀ →* MulAut H where
  toFun g := e.symm.trans ((C25Y.layerAut J (hL g g.2)).trans e)
  map_one' := by
    ext y
    simp only [MulEquiv.trans_apply, MulAut.one_apply]
    rw [show (e.symm y) = QuotientGroup.mk (Quotient.out (e.symm y)) from
      (QuotientGroup.out_eq' _).symm, C25Y.layerAut_mk]
    rw [show C25Y.conjOnSub J (hL 1 (one_mem _)) (Quotient.out (e.symm y)) =
      Quotient.out (e.symm y) from Subtype.ext (by simp [C25Y.coe_conjOnSub])]
    rw [QuotientGroup.out_eq', MulEquiv.apply_symm_apply]
  map_mul' g h := by
    ext y
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.symm_apply_apply]
    congr 1
    induction e.symm y using QuotientGroup.induction_on with
    | H x =>
      rw [C25Y.layerAut_mk, C25Y.layerAut_mk, C25Y.layerAut_mk]
      congr 1
      apply Subtype.ext
      simp only [C25Y.coe_conjOnSub, Subgroup.coe_mul]
      group

theorem quotAutHom_eq_one_iff [Finite G] {H : Type} [Group H] {J L₀ : Subgroup G}
    {hL : ∀ g ∈ L₀, conjSub g J = J} {e : ↥J ⧸ classicalInvolutionOddCore ↥J ≃* H} (g : ↥L₀) :
    quotAutHom J L₀ hL e g = 1 ↔ (g : G) ∈ trivialOnQuot J := by
  rw [← layerAut_eq_id_iff J (hL g g.2)]
  constructor
  · intro h y
    have h1 := congrArg (fun α : MulAut H => α (e y)) h
    simp only [quotAutHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    exact e.injective h1
  · intro h
    ext y
    simp only [quotAutHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply, h,
      MulEquiv.apply_symm_apply, MulAut.one_apply]

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem normalizes_of_perfect [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a)
    {L₀ : Subgroup G} (hLz : L₀ ≤ Subgroup.centralizer ({z} : Set G)) (hLp : ⁅L₀, L₀⁆ = L₀) :
    ∀ g ∈ L₀, conjSub g K = K ∧ conjSub g K' = K' := by
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hKK : K ≠ K' := hs.hne.symm
  have hcz : ∀ x ∈ Subgroup.centralizer ({z} : Set G), x * z * x⁻¹ = z := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx]; group
  have hpair := fun x hx => C25Y.conjSub_pair_of_central hs (hcz x hx)
  have hmul : ∀ x ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Subgroup.centralizer ({z} : Set G),
      (conjSub (x * y) K = K ↔ (conjSub x K = K ↔ conjSub y K = K)) := by
    intro x hx y hy
    rw [conjSub_mul]
    rcases hpair x hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
      rcases hpair y hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · simp [hx1, hy1]
    · rw [hy1, hx2]; simp [hx1, hKK.symm]
    · rw [hy1, hx1]; simp [hKK.symm]
    · rw [hy1, hx2]; simp [hx1, hKK.symm]
  have hinv : ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      (conjSub x⁻¹ K = K ↔ conjSub x K = K) := by
    intro x _
    constructor
    · intro h
      have := congrArg (conjSub x) h
      rwa [conjSub_conjSub_inv, eq_comm] at this
    · intro h
      have := congrArg (conjSub x⁻¹) h
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, eq_comm] at this
  have hK : ∀ g ∈ L₀, conjSub g K = K := by
    have hle : ⁅L₀, L₀⁆ ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.commutator_le]
      intro g hg h hh
      have hgz := hLz hg
      have hhz := hLz hh
      have hgi := Subgroup.inv_mem _ hgz
      have hhi := Subgroup.inv_mem _ hhz
      refine mem_normalizer_of_conjSub_eq ?_
      rw [commutatorElement_def]
      have e1 := hmul _ (mul_mem (mul_mem hgz hhz) hgi) _ hhi
      have e2 := hmul _ (mul_mem hgz hhz) _ hgi
      have e3 := hmul _ hgz _ hhz
      have e4 := hinv _ hgz
      have e5 := hinv _ hhz
      tauto
    intro g hg
    rw [← hLp] at hg
    exact conjSub_eq_of_mem_normalizer (hle hg)
  intro g hg
  refine ⟨hK g hg, ?_⟩
  rcases hpair g (hLz hg) with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd ((hK g hg).symm.trans h1) hKK

theorem A_comm (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {b b' : G}
    (hb : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb' : b' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) :
    b * b' = b' * b := by
  have haz := C.comm
  have hgen : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x * a = a * x ∧ x * z = z * x := by
    intro x hx
    rcases C.hA0 x hx with h | h | h | h <;> rw [h]
    · simp
    · exact ⟨rfl, haz⟩
    · exact ⟨haz.symm, rfl⟩
    · constructor
      · calc a * z * a = a * (z * a) := by group
          _ = a * (a * z) := by rw [haz]
      · calc a * z * z = a * z * z := rfl
          _ = z * (a * z) := by rw [mul_assoc, ← mul_assoc z, ← haz]; group
  obtain ⟨h1, h2⟩ := hgen b hb
  rcases C.hA0 b' hb' with h | h | h | h <;> rw [h]
  · simp
  · exact h1
  · exact h2
  · calc b * (a * z) = (b * a) * z := by group
      _ = a * (b * z) := by rw [h1]; group
      _ = a * z * b := by rw [h2]; group

theorem comm_mem_oddCore_cOne [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a)
    {x y : G} (hx : x ∈ cOne z K K') (hy : y ∈ cOne z K K') :
    ⁅x, y⁆ ∈ oddCoreIn (cOne z K K') := by
  obtain ⟨o, ho, b, hb, rfl⟩ := C.cOne_eq_mul x hx
  obtain ⟨o', ho', b', hb', rfl⟩ := C.cOne_eq_mul y hy
  have hbC : b ∈ cOne z K K' := C.A_le_cOne hb
  have hb'C : b' ∈ cOne z K K' := C.A_le_cOne hb'
  have hbb := C.A_comm hb hb'
  have hn₁ : b * o' * b⁻¹ ∈ oddCoreIn (cOne z K K') := conj_mem_oddCoreIn hbC ho'
  have hn₂ : b' * o * b'⁻¹ ∈ oddCoreIn (cOne z K K') := conj_mem_oddCoreIn hb'C ho
  have e : ⁅o * b, o' * b'⁆ = (o * (b * o' * b⁻¹)) * (o' * (b' * o * b'⁻¹))⁻¹ := by
    calc ⁅o * b, o' * b'⁆ = (o * (b * o' * b⁻¹)) * (b * b') *
          ((o' * (b' * o * b'⁻¹)) * (b' * b))⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (o * (b * o' * b⁻¹)) * (o' * (b' * o * b'⁻¹))⁻¹ := by rw [hbb]; group
  rw [e]
  exact mul_mem (mul_mem ho hn₁) (inv_mem (mul_mem ho' hn₂))

theorem card_le_of_perfect [IsSimpleGroup G] (hM7 : SL2PerfectAut p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a)
    {L₀ : Subgroup G} (hLz : L₀ ≤ Subgroup.centralizer ({z} : Set G)) (hLp : ⁅L₀, L₀⁆ = L₀)
    {Q : Type} [Group Q] [IsSimpleGroup Q] (hQ : ∃ x y : Q, x * y ≠ y * x)
    (φ : ↥L₀ →* Q) (hφ : Function.Surjective φ) :
    4 * Nat.card Q ≤ Nat.card (SL(2, GaloisField p f)) ^ 2 := by
  classical
  have : Finite Q := Finite.of_surjective φ hφ
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnorm := C.normalizes_of_perfect hLz hLp
  obtain ⟨zK, hzK⟩ := hΩ.classical K hs.stand.mem
  obtain ⟨zK', hzK'⟩ := hΩ.classical K' hs.hK'.1
  obtain ⟨e⟩ := hzK.nonempty_equiv
  obtain ⟨e'⟩ := hzK'.nonempty_equiv
  set ρ := quotAutHom K L₀ (fun g hg => (hnorm g hg).1) e with hρ
  set ρ' := quotAutHom K' L₀ (fun g hg => (hnorm g hg).2) e' with hρ'
  have hperf : commutator ↥L₀ = ⊤ := by
    apply Subgroup.map_injective L₀.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hLp]
  have hsmall : ∀ σ : ↥L₀ →* MulAut (SL(2, GaloisField p f)),
      2 * Nat.card σ.range ≤ Nat.card (SL(2, GaloisField p f)) := by
    intro σ
    refine hM7 hp hq σ.range ?_
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]
  set N := ρ.ker ⊓ ρ'.ker with hN
  have hNC : ∀ g ∈ N, (g : G) ∈ cOne z K K' := by
    intro g hg
    exact ⟨⟨hLz g.2, (quotAutHom_eq_one_iff g).mp hg.1⟩, (quotAutHom_eq_one_iff g).mp hg.2⟩
  set O₁ := (oddCoreIn (cOne z K K')).comap L₀.subtype with hO₁
  have hcommN : ⁅N, N⁆ ≤ O₁ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    show ((⁅x, y⁆ : ↥L₀) : G) ∈ oddCoreIn (cOne z K K')
    rw [show ((⁅x, y⁆ : ↥L₀) : G) = ⁅(x : G), (y : G)⁆ from rfl]
    exact C.comm_mem_oddCore_cOne (hNC x hx) (hNC y hy)
  have hO₁odd : Odd (Nat.card O₁) := by
    have h1 : Nat.card (O₁.map L₀.subtype) = Nat.card O₁ :=
      Subgroup.card_map_of_injective L₀.subtype_injective
    have h2 : O₁.map L₀.subtype ≤ oddCoreIn (cOne z K K') := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le h2)
  have hNn : (N.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map φ) with hbot | htop
  ·
    have hNk : N ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hQcard : Nat.card Q = φ.ker.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    have h1 : φ.ker.index ≤ N.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hNk)
    have h2 : N.index ≤ ρ.ker.index * ρ'.ker.index := Subgroup.index_inf_le
    rw [Subgroup.index_ker, Subgroup.index_ker] at h2
    have h3 := hsmall ρ
    have h4 := hsmall ρ'
    calc 4 * Nat.card Q ≤ 4 * (Nat.card ρ.range * Nat.card ρ'.range) := by
          rw [hQcard]; exact Nat.mul_le_mul_left _ (h1.trans h2)
      _ = (2 * Nat.card ρ.range) * (2 * Nat.card ρ'.range) := by ring
      _ ≤ Nat.card (SL(2, GaloisField p f)) * Nat.card (SL(2, GaloisField p f)) :=
          Nat.mul_le_mul h3 h4
      _ = Nat.card (SL(2, GaloisField p f)) ^ 2 := by ring
  ·
    exfalso
    have hQperf : commutator Q = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hQ
        apply hxy
        have hc : ⁅x, y⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
          (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    have hO₁top : O₁.map φ = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hQperf, commutator_def, ← htop, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hcommN
    have hQodd : Odd (Nat.card Q) := by
      have h1 : Nat.card (O₁.map φ) ∣ Nat.card O₁ := Subgroup.card_map_dvd _ _
      rw [hO₁top, Subgroup.card_top] at h1
      exact Odd.of_dvd_nat hO₁odd h1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
    obtain ⟨x, y, hxy⟩ := hQ
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv x y)

theorem not_hasBigFix [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {b c : G} (hb2 : b * b = 1)
    (hbX : conjSub b (exactLayer Ω a) = exactLayer Ω a) (hcb : c * z * c⁻¹ = b) :
    ¬ HasBigFix p f (C25Y.layerAut (exactLayer Ω a) hbX) := by
  classical
  rintro ⟨L, hLfix, hLs, hLnc, hLcard⟩
  set H₁ : Subgroup ↥(exactLayer Ω a) :=
    L.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a))) ⊓
    (Subgroup.centralizer ({b} : Set G)).comap (exactLayer Ω a).subtype with hH₁
  have hH₁map : H₁.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a))) = L := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro l hl
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective l
      have hfix := hLfix _ hl
      rw [layerAut_mk_eq_iff] at hfix
      have hy : (y₀ : G)⁻¹ * b * (y₀ : G) * b ∈ oddCoreIn (exactLayer Ω a) := by
        have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
        have h1 := conj_mem_oddCoreIn ((exactLayer Ω a).inv_mem y₀.2) hfix
        have e : (y₀ : G)⁻¹ * ⁅b, (y₀ : G)⁆ * (y₀ : G)⁻¹⁻¹ = (y₀ : G)⁻¹ * b * (y₀ : G) * b := by
          rw [commutatorElement_def, hbi]; group
        rwa [e] at h1
      obtain ⟨o, ho, hoc⟩ := exists_mul_comm_of_odd (odd_card_oddCoreIn (exactLayer Ω a)) hb2 hy
      have hoX : o ∈ exactLayer Ω a := oddCoreIn_le (exactLayer Ω a) ho
      refine ⟨y₀ * ⟨o, hoX⟩, ⟨?_, ?_⟩, ?_⟩
      · show QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a)) (y₀ * ⟨o, hoX⟩) ∈ L
        rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (mk_eq_one_iff (exactLayer Ω a) ⟨o, hoX⟩).mpr ho, mul_one]
        exact hl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hoc
      · rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          (mk_eq_one_iff (exactLayer Ω a) ⟨o, hoX⟩).mpr ho, mul_one]
  have hLperf : ⁅L, L⁆ = L := by
    have hc : commutator ↥L = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hLnc
        apply hxy
        have hc : ⁅x, y⁆ ∈ commutator ↥L :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    have := congrArg (Subgroup.map L.subtype) hc
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at this
  have hex : ∃ n : ℕ, ∃ H₀ : Subgroup ↥(exactLayer Ω a), H₀ ≤ H₁ ∧
      H₀.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a))) = L ∧
      Nat.card H₀ = n := ⟨_, H₁, le_rfl, hH₁map, rfl⟩
  obtain ⟨H₀, hH₀le, hH₀map, hH₀card⟩ := Nat.find_spec hex
  have hH₀perf : ⁅H₀, H₀⁆ = H₀ := by
    have hle : ⁅H₀, H₀⁆ ≤ H₀ := Subgroup.commutator_le_self _
    have hmap :
        (⁅H₀, H₀⁆).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a))) = L := by
      rw [Subgroup.map_commutator, hH₀map, hLperf]
    have hmin := Nat.find_min' hex ⟨⁅H₀, H₀⁆, hle.trans hH₀le, hmap, rfl⟩
    rw [← hH₀card] at hmin
    exact Subgroup.eq_of_le_of_card_ge hle hmin
  have hH₀L : ∀ y ∈ H₀,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a)) y ∈ L :=
    fun y hy => (hH₀le hy).1
  set L₀ : Subgroup G := (H₀.map (exactLayer Ω a).subtype).map (MulAut.conj c⁻¹).toMonoidHom
    with hL₀
  have hL₀z : L₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyb : (y : G) * b = b * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hH₀le hy).2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hz : z = c⁻¹ * b * c := by rw [← hcb]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    rw [hz]
    calc c⁻¹ * (y : G) * c * (c⁻¹ * b * c) = c⁻¹ * ((y : G) * b) * c := by group
      _ = c⁻¹ * (b * (y : G)) * c := by rw [hyb]
      _ = c⁻¹ * b * c * (c⁻¹ * (y : G) * c) := by group
  have hL₀p : ⁅L₀, L₀⁆ = L₀ := by
    rw [hL₀, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hH₀perf]
  let ψ : ↥H₀ →* ↥L :=
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a))).comp H₀.subtype).codRestrict
      L (fun y => hH₀L y y.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨l, hl⟩
    rw [← hH₀map] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    exact ⟨⟨y, hy⟩, rfl⟩
  let e₁ := Subgroup.equivMapOfInjective H₀ (exactLayer Ω a).subtype
    (exactLayer Ω a).subtype_injective
  let e₂ := Subgroup.equivMapOfInjective (H₀.map (exactLayer Ω a).subtype)
    (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
  let φ : ↥L₀ →* ↥L := ψ.comp (e₁.trans e₂).symm.toMonoidHom
  have hφ : Function.Surjective φ := hψ.comp (e₁.trans e₂).symm.surjective
  have h4 := C.card_le_of_perfect hM.sl2PerfectAut hL₀z hL₀p hLnc φ hφ
  omega

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
