module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.GH74.Uniqueness.SU.SU1Normal0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem u43_mem_core_iff {p : ℕ} {J : Subgroup G} (x : J) :
    x ∈ GLAPPrimeCore p ↥J ↔ (x : G) ∈ GLAPPrimeCoreOf p J :=
  (Subgroup.mem_map_iff_mem J.subtype_injective).symm

private theorem u43_mk_comm_iff {p : ℕ} {J : Subgroup G} (a b : J) :
    (QuotientGroup.mk a : PQuot p J) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a ↔
      ⁅(a : G), (b : G)⁆ ∈ GLAPPrimeCoreOf p J := by
  have e1 : ⁅(QuotientGroup.mk a : PQuot p J), QuotientGroup.mk b⁆ =
      QuotientGroup.mk ⁅a, b⁆ :=
    (map_commutatorElement (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) a b).symm
  rw [← commutatorElement_eq_one_iff_mul_comm, e1, QuotientGroup.eq_one_iff,
    u43_mem_core_iff]
  rfl

private theorem u43_centMod_iff_mem_center {p : ℕ} {J : Subgroup G} (x : J) :
    (x : G) ∈ centModSubgroup p J ↔
      (QuotientGroup.mk x : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
  rw [mem_centModSubgroup, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hc⟩ g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    exact (u43_mk_comm_iff j x).2 (hc (j : G) j.2)
  · intro hc
    exact ⟨Subgroup.le_normalizer x.2, fun l hl => (u43_mk_comm_iff ⟨l, hl⟩ x).1 (hc _)⟩

private theorem u43_conj_mem_core {p : ℕ} {J : Subgroup G} {b x : G}
    (hinner : InducesInnerMod p J b) (hx : x ∈ J) (hxc : x ∈ centModSubgroup p J) :
    x⁻¹ * (b⁻¹ * x * b) ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨l, hl, hy⟩ := hinner
  have hu : (l⁻¹ * x * l)⁻¹ * (b⁻¹ * x * b) ∈ GLAPPrimeCoreOf p J := hy x hx
  have h1 : ⁅l⁻¹, x⁻¹⁆ ∈ GLAPPrimeCoreOf p J :=
    (mem_centModSubgroup.1 (Subgroup.inv_mem _ hxc)).2 l⁻¹ (J.inv_mem hl)
  have hv : x⁻¹ * l⁻¹ * x * l ∈ GLAPPrimeCoreOf p J := by
    have e : x⁻¹ * l⁻¹ * x * l = (⁅l⁻¹, x⁻¹⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have key : x⁻¹ * (b⁻¹ * x * b) =
      (x⁻¹ * l⁻¹ * x * l) * ((l⁻¹ * x * l)⁻¹ * (b⁻¹ * x * b)) := by group
  rw [key]
  exact Subgroup.mul_mem _ hv hu

private theorem u43_exists_exponent_sub {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hZp : IsPGroup p (Subgroup.center K)) (hZ : ¬ IsCyclic (Subgroup.center K)) :
    ∃ W : Subgroup K, W ≤ Subgroup.center K ∧ (∀ k ∈ W, k ^ p = 1) ∧ p ^ 2 ∣ Nat.card W := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup (Subgroup.center K) :=
    { (inferInstance : Group (Subgroup.center K)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a.1) }
  let Ω : Subgroup (Subgroup.center K) :=
    (powMonoidHom p : Subgroup.center K →* Subgroup.center K).ker
  have hΩmem : ∀ x : Subgroup.center K, x ∈ Ω ↔ x ^ p = 1 := fun x => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
  have hΩcard : Nat.card Ω = Nat.card {x : Subgroup.center K // x ^ p = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight hΩmem)
  have hΩp : IsPGroup p Ω := fun g => ⟨1, Subtype.ext (by
    simpa using (hΩmem g.1).1 g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hΩp
  have hlt : p < Nat.card Ω := by
    by_contra hle
    have hle' : Nat.card Ω ≤ p := not_lt.1 hle
    obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 hZp
    apply hZ
    apply CFSG.GH74.Uniqueness.SU.SU1.isCyclic_of_card_roots_le hp e (Subgroup.center K) he
    rw [← hΩcard]
    exact hle'
  have hn2 : 2 ≤ n := by
    by_contra h
    have h' : n = 0 ∨ n = 1 := by omega
    rcases h' with rfl | rfl
    · rw [hn, pow_zero] at hlt
      have := hp.two_le
      omega
    · rw [hn, pow_one] at hlt
      omega
  refine ⟨Ω.map (Subgroup.center K).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    simpa using congrArg Subtype.val ((hΩmem z).1 hz)
  · rw [Subgroup.card_map_of_injective (Subgroup.center K).subtype_injective, hn]
    exact pow_dvd_pow p hn2

private theorem u43_mem_normalizer_sup {H K N : Subgroup G} {g : G} (hgN : g ∈ N)
    (hconj : ∀ x ∈ N, (∀ s ∈ H, x * s * x⁻¹ ∈ H ⊔ K) ∧ (∀ s ∈ K, x * s * x⁻¹ ∈ H ⊔ K)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ x ∈ N, ∀ s ∈ H ⊔ K, x * s * x⁻¹ ∈ H ⊔ K := by
    intro x hx
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj x).toMonoidHom :=
      sup_le (fun s hs => (hconj x hx).1 s hs) (fun s hs => (hconj x hx).2 s hs)
    intro s hs
    exact hle hs
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    exact key g hgN s hs
  · intro hs
    have h := key g⁻¹ (N.inv_mem hgN) _ hs
    have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    rwa [e] at h

private theorem u43_inf_core_eq_bot {J : Subgroup G} {p : ℕ} (hp : p.Prime) {P : Subgroup J}
    (hP : Nat.card P = p ^ 2) : P ⊓ GLAPPrimeCore p ↥J = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
  have h1 : Nat.card (P ⊓ GLAPPrimeCore p ↥J : Subgroup J) ∣ p ^ 2 := by
    rw [← hP]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (P ⊓ GLAPPrimeCore p ↥J : Subgroup J) ∣ Nat.card (GLAPPrimeCore p ↥J) :=
    Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.Coprime (Nat.card (P ⊓ GLAPPrimeCore p ↥J : Subgroup J)) p :=
    Nat.Coprime.coprime_dvd_left h2 hcop.symm
  have h4 : Nat.card (P ⊓ GLAPPrimeCore p ↥J : Subgroup J) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 h3) h1
  exact Subgroup.eq_bot_of_card_eq _ h4

theorem not_isCyclic_inf_of_not_isCyclic_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X B J T : Subgroup G} (hB : GLAIsBmax p B) (hJ : GLAPComponent p X J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p J)))
    (hTJ : T ≤ J) (hTne : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hZ : ¬ IsCyclic (Subgroup.center (PQuot p J)))
    (hinner : ∀ b ∈ B, InducesInnerMod p J b) : ¬ IsCyclic (B ⊓ J : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJN : J ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf p J
  have hBN : B ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    fun b hb => normalizer_le_normalizer_glaPPrimeCoreOf p J (hBJ hb)
  have hOJ : GLAPPrimeCoreOf p J ≤ J := Subgroup.map_subtype_le _
  have hOcop : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p J) := by
    have h1 : Nat.card (GLAPPrimeCoreOf p J) = Nat.card (GLAPPrimeCore p ↥J) :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hTN : T ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    fun t ht => hJN (hTJ ht)
  have hTp : ¬ p ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
    rw [hn]
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hcore : GLAPPrimeCore p (PQuot p J) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥J) p
  have hZp : IsPGroup p (Subgroup.center (PQuot p J)) := isPGroup_center hp hcore
  obtain ⟨W, hWZ, hWexp, hWdvd⟩ := u43_exists_exponent_sub hp hZp hZ
  let π : J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  let C : Subgroup J := (W.comap π) ⊓ ((Subgroup.centralizer (B : Set G)).subgroupOf J)
  have hsurj : ∀ k ∈ W, ∃ c ∈ C, π c = k := by
    intro k hk
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) k
    have hx₀ : (x₀ : G) ∈ centModSubgroup p J :=
      (u43_centMod_iff_mem_center x₀).2 (hWZ hk)
    have hy : ∀ a ∈ B, (x₀ : G)⁻¹ * (a * (x₀ : G) * a⁻¹) ∈ GLAPPrimeCoreOf p J := by
      intro a ha
      have h := u43_conj_mem_core (hinner a⁻¹ (B.inv_mem ha)) x₀.2 hx₀
      simpa only [inv_inv] using h
    obtain ⟨n, hn, hcent⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.Generation228.exists_fixed_mem_coset hp
        (isPGroup_of_isElemAbelian hB.1) hBN hOcop hy
    have hn' : (⟨n, hOJ hn⟩ : J) ∈ GLAPPrimeCore p ↥J := (u43_mem_core_iff _).2 hn
    have hπn : π ⟨n, hOJ hn⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hn'
    have hπc : π ⟨(x₀ : G) * n, J.mul_mem x₀.2 (hOJ hn)⟩ = π x₀ := by
      have e : (⟨(x₀ : G) * n, J.mul_mem x₀.2 (hOJ hn)⟩ : J) = x₀ * ⟨n, hOJ hn⟩ :=
        Subtype.ext rfl
      rw [e, map_mul, hπn, mul_one]
    refine ⟨⟨(x₀ : G) * n, J.mul_mem x₀.2 (hOJ hn)⟩, ⟨?_, ?_⟩, hπc⟩
    · exact Subgroup.mem_comap.2 (by rw [hπc]; exact hk)
    · exact Subgroup.mem_subgroupOf.2 hcent
  have hCW : C.map π = W := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hc.1
    · intro k hk
      obtain ⟨c, hc, hck⟩ := hsurj k hk
      exact ⟨c, hc, hck⟩
  have hCdvd : p ^ 2 ∣ Nat.card C := by
    have h1 := Subgroup.card_map_dvd C π
    rw [hCW] at h1
    exact dvd_trans hWdvd h1
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime p hCdvd
  let PJ : Subgroup J := P'.map C.subtype
  have hPJcard : Nat.card PJ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hP'
  have hPJC : ∀ x ∈ PJ, x ∈ C := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hPJW : ∀ x ∈ PJ, π x ∈ W := fun x hx => (hPJC x hx).1
  have hPJcomm : ∀ x ∈ PJ, ∀ y ∈ PJ, x * y = y * x := by
    intro x hx y hy
    have hcomm : π x * π y = π y * π x :=
      Subgroup.mem_center_iff.1 (hWZ (hPJW y hy)) (π x)
    have h1 : π ((x * y)⁻¹ * (y * x)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm, inv_mul_cancel]
    have hmem : (x * y)⁻¹ * (y * x) ∈ PJ ⊓ GLAPPrimeCore p ↥J :=
      ⟨PJ.mul_mem (PJ.inv_mem (PJ.mul_mem hx hy)) (PJ.mul_mem hy hx),
        (QuotientGroup.eq_one_iff ((x * y)⁻¹ * (y * x))).1 h1⟩
    rw [u43_inf_core_eq_bot hp hPJcard, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.1 hmem
  have hPJexp : ∀ x ∈ PJ, x ^ p = 1 := by
    intro x hx
    have h1 : π (x ^ p) = 1 := by
      rw [map_pow]
      exact hWexp _ (hPJW x hx)
    have hmem : x ^ p ∈ PJ ⊓ GLAPPrimeCore p ↥J :=
      ⟨PJ.pow_mem hx p, (QuotientGroup.eq_one_iff (x ^ p)).1 h1⟩
    rw [u43_inf_core_eq_bot hp hPJcard, Subgroup.mem_bot] at hmem
    exact hmem
  let PG : Subgroup G := PJ.map J.subtype
  have hPGcard : Nat.card PG = p ^ 2 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hPJcard
  have hPGJ : PG ≤ J := Subgroup.map_subtype_le _
  have hPGCM : PG ≤ centModSubgroup p J := by
    rintro _ ⟨x, hx, rfl⟩
    exact (u43_centMod_iff_mem_center x).2 (hWZ (hPJW x hx))
  have hPGcomm : ∀ d ∈ B, ∀ c ∈ PG, d * c = c * d := by
    rintro d hd _ ⟨x, hx, rfl⟩
    have hxc : ((x : J) : G) ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.mem_subgroupOf.1 (hPJC x hx).2
    exact Subgroup.mem_centralizer_iff.1 hxc d hd
  have hPGel : IsElemAbelian p PG := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hxa, ← hyb]
      exact congrArg Subtype.val (hPJcomm x hx y hy)
    · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 ha
      rw [← hxa]
      exact congrArg Subtype.val (hPJexp x hx)
  have hE : IsElemAbelian p (B ⊔ PG) := Prop53.isElemAbelian_sup_of_commute hB.1 hPGel hPGcomm
  have hconjCM : ∀ w ∈ centModSubgroup p J,
      (∀ s ∈ GLAPPrimeCoreOf p J, w * s * w⁻¹ ∈ GLAPPrimeCoreOf p J ⊔ T) ∧
        (∀ s ∈ T, w * s * w⁻¹ ∈ GLAPPrimeCoreOf p J ⊔ T) := by
    intro w hw
    have hwN : w ∈ Subgroup.normalizer (J : Set G) := (mem_centModSubgroup.1 hw).1
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1
        (normalizer_le_normalizer_glaPPrimeCoreOf p J hwN) s).1 hs)
    · have hsJ : s ∈ J := hTJ hs
      have h1 : ⁅s⁻¹, w⁆ ∈ GLAPPrimeCoreOf p J :=
        (mem_centModSubgroup.1 hw).2 s⁻¹ (J.inv_mem hsJ)
      have e : ⁅s⁻¹, w⁆ = s⁻¹ * (w * s * w⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e] at h1
      have e2 : w * s * w⁻¹ = s * (s⁻¹ * (w * s * w⁻¹)) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left h1)
  have hconjB : ∀ b ∈ B, (∀ s ∈ GLAPPrimeCoreOf p J, b * s * b⁻¹ ∈ GLAPPrimeCoreOf p J ⊔ T) ∧
      (∀ s ∈ T, b * s * b⁻¹ ∈ GLAPPrimeCoreOf p J ⊔ T) := fun b hb =>
    ⟨fun s hs => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hBN hb) s).1 hs),
      fun s hs => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hBT hb) s).1 hs)⟩
  have hES : B ⊔ PG ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p J ⊔ T : Subgroup G) : Set G) :=
    sup_le (fun b hb => u43_mem_normalizer_sup hb hconjB)
      (fun w hw => u43_mem_normalizer_sup (hPGCM hw) hconjCM)
  have hSp : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p J ⊔ T : Subgroup G) :=
    not_dvd_card_sup_of_le_normalizer hp hTN hOcop hTp
  have hbot : B ⊔ PG ≤ Subgroup.normalizer (((⊥ : Subgroup G)) : Set G) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710 in
  obtain ⟨Q, -, -, hQ2, hQrel, hEQ⟩ :=
    exists_invariant_sylow_containing_of_pGroup hp Nat.prime_two (A := B ⊔ PG)
      (K := GLAPPrimeCoreOf p J ⊔ T) (T := ⊥) (isPGroup_of_isElemAbelian hE) hES hSp bot_le
      (IsPGroup.of_card (n := 0) (by simp)) hbot
  have hTcard : 2 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hTne
      apply Subgroup.eq_bot_of_card_eq
      rw [hn, pow_zero]
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hQrel
    rw [hQ, Subgroup.relIndex_bot_left]
    exact dvd_trans hTcard
      (Subgroup.card_dvd_of_le (le_sup_right : T ≤ GLAPPrimeCoreOf p J ⊔ T))
  have hEB : B ⊔ PG = B :=
    GLAIsBmax.eq_of_le hp hB le_sup_left hE hQne hQ2 hEQ
  have hPGB : PG ≤ B := le_sup_right.trans hEB.le
  intro hcyc
  have hPGBJ : PG ≤ B ⊓ J := le_inf hPGB hPGJ
  haveI : IsCyclic (PG.subgroupOf (B ⊓ J)) := Subgroup.isCyclic _
  haveI : Fintype (PG.subgroupOf (B ⊓ J)) := Fintype.ofFinite _
  have hQcard : Nat.card (PG.subgroupOf (B ⊓ J)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPGBJ).toEquiv, hPGcard]
  have hexp : ∀ a : PG.subgroupOf (B ⊓ J), a ^ p = 1 := fun a =>
    Subtype.ext (Subtype.ext (by simpa using hPGel.2 _ (Subgroup.mem_subgroupOf.1 a.2)))
  have hle := IsCyclic.card_pow_eq_one_le (α := PG.subgroupOf (B ⊓ J)) (n := p) hp.pos
  have hfilt : (Finset.univ.filter fun a : PG.subgroupOf (B ⊓ J) => a ^ p = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun a _ => hexp a
  rw [hfilt, Finset.card_univ, ← Nat.card_eq_fintype_card, hQcard] at hle
  have h2 := hp.two_le
  have h3 : p < p ^ 2 := by nlinarith
  omega

end CFSG.LocalAnalysis.GLTheoremA.P55
