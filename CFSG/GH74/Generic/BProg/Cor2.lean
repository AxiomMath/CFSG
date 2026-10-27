module

public import CFSG.GH74.Generic.BProg.Cor2Easy
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.Theta32

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Bg.Thompson Subgroup MulAction
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_sylow_two {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsPGroup 2 E) (P : Sylow 2 X) :
    ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup X) (hQ hy)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

theorem prop92 {M : Subgroup G} (h2 : Stage2Concl2 M) {y₁ y₂ : G}
    (hconj : ∃ g : G, g * y₁ * g⁻¹ = y₂) {B : Subgroup G} (hB : InU0 M B)
    (hBy : ∀ b ∈ B, b * y₁ = y₁ * b) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer ({y₂} : Set G))) (hSM : S ≤ M) :
    ∃ m ∈ M, m * y₁ * m⁻¹ = y₂ := by
  obtain ⟨g, hg⟩ := hconj
  set C : Subgroup G := centralizer ({y₂} : Set G) with hC
  obtain ⟨hBM, hBel, -⟩ := hB.1
  have hBp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  set H : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hH
  have hHC : H ≤ C := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    show (g * b * g⁻¹) * y₂ = y₂ * (g * b * g⁻¹)
    rw [← hg]
    calc (g * b * g⁻¹) * (g * y₁ * g⁻¹) = g * (b * y₁) * g⁻¹ := by group
      _ = g * (y₁ * b) * g⁻¹ := by rw [hBy b hb]
      _ = (g * y₁ * g⁻¹) * (g * b * g⁻¹) := by group
  have hHp : IsPGroup 2 H := hBp.map _
  obtain ⟨Q, hQ⟩ := hS
  have hH' : IsPGroup 2 (H.subgroupOf C) := hHp.comap_subtype
  obtain ⟨c, hc⟩ := exists_conj_le_sylow_two hH' Q
  have hcg : ∀ b ∈ B, ((c : G) * (g * b * g⁻¹) * (c : G)⁻¹) ∈ S := by
    intro b hb
    have hmem : (⟨g * b * g⁻¹, hHC ⟨b, hb, rfl⟩⟩ : C) ∈ H.subgroupOf C :=
      Subgroup.mem_subgroupOf.2 ⟨b, hb, rfl⟩
    have h1 := hc ⟨_, hmem, rfl⟩
    rw [← hQ]
    exact ⟨_, h1, rfl⟩
  have hcgM : conjugate B ((c : G) * g)⁻¹ ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    refine hSM ?_
    have e : (MulAut.conj ((c : G) * g)⁻¹⁻¹).toMonoidHom b =
        (c : G) * (g * b * g⁻¹) * (c : G)⁻¹ := by
      show ((c : G) * g)⁻¹⁻¹ * b * ((c : G) * g)⁻¹⁻¹⁻¹ = _
      group
    rw [e]
    exact hcg b hb
  have hmM : ((c : G) * g)⁻¹ ∈ M := h2 B hB _ hcgM
  refine ⟨(c : G) * g, by simpa using M.inv_mem hmM, ?_⟩
  have hcy : (c : G) * y₂ = y₂ * (c : G) := by
    have hcmem : (c : G) ∈ centralizer ({y₂} : Set G) := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hcmem
    exact hcmem
  calc (c : G) * g * y₁ * ((c : G) * g)⁻¹ = (c : G) * (g * y₁ * g⁻¹) * (c : G)⁻¹ := by group
    _ = (c : G) * y₂ * (c : G)⁻¹ := by rw [hg]
    _ = y₂ := by rw [hcy]; group


theorem exists_hom_cyclic_of_not_mem_derived (M : Subgroup G) {y : G} (hy : y ∈ M)
    (hny : y ∉ derivedIn M) :
    ∃ (n : ℕ) (φ : ↥M →* Multiplicative (ZMod n)), φ ⟨y, hy⟩ ≠ 1 := by
  classical
  have ha : (Abelianization.of (⟨y, hy⟩ : ↥M)) ≠ 1 := by
    intro h
    apply hny
    have h1 : (⟨y, hy⟩ : ↥M) ∈ (Abelianization.of : ↥M →* Abelianization ↥M).ker := h
    rw [Abelianization.ker_of] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨ι, hι, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite (Abelianization ↥M)
  have hne : e (Abelianization.of (⟨y, hy⟩ : ↥M)) ≠ 1 := by
    intro h
    exact ha (e.injective (by rw [h, map_one]))
  have : ∃ i, e (Abelianization.of (⟨y, hy⟩ : ↥M)) i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨i, hi⟩ := this
  exact ⟨n i, (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp
    (e.toMonoidHom.comp Abelianization.of), hi⟩


omit [Finite G] in
theorem exists_sylow_two_ge_of_commute {B : Subgroup G} (hBel : IsElementaryAbelian 2 ↥B) {y : G}
    (hy2 : orderOf y = 2) (hyB : ∀ b ∈ B, b * y = y * b) :
    ∃ P : Sylow 2 G, B ≤ P ∧ y ∈ P := by
  have hBp : IsPGroup 2 B := IsElementaryAbelian.isPGroup 2 B
  obtain ⟨hab, -⟩ := CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set C : Subgroup G := centralizer (B : Set G) with hC
  have hBC : B ≤ C := fun b hb => Subgroup.mem_centralizer_iff.2 fun h hh => hab h hh b hb
  have hyC : y ∈ C := Subgroup.mem_centralizer_iff.2 fun h hh => hyB h hh
  have hN : (B.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (c : G) ∈ centralizer (B : Set G) := c.2
    have h1 := Subgroup.mem_centralizer_iff.1 hc (n : G) hn
    have : (c : G) * (n : G) * (c : G)⁻¹ = (n : G) := by
      rw [← h1]; group
    show (c : G) * (n : G) * (c : G)⁻¹ ∈ B
    rw [this]; exact hn
  have hNp : IsPGroup 2 (B.subgroupOf C) := hBp.comap_subtype
  set y' : ↥C := ⟨y, hyC⟩ with hy'
  have hy'p : IsPGroup 2 (zpowers y') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : orderOf y' = 2 := by
      rw [← orderOf_injective C.subtype C.subtype_injective y']
      exact hy2
    exact this
  obtain ⟨R, hR⟩ := hy'p.exists_le_sylow
  have hNR : B.subgroupOf C ≤ R := IsPGroup.le_sylow_of_normal hNp R
  have hPy : IsPGroup 2 ((R : Subgroup C).map C.subtype) := R.isPGroup'.map _
  obtain ⟨P, hP⟩ := hPy.exists_le_sylow
  refine ⟨P, fun b hb => hP ⟨⟨b, hBC hb⟩, hNR (Subgroup.mem_subgroupOf.2 hb), rfl⟩,
    hP ⟨y', hR (Subgroup.mem_zpowers y'), rfl⟩⟩


theorem prop93 (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {M : Subgroup G}
    (h2 : Stage2Concl2 M)
    (hc : ∀ X B : Subgroup G, IsPGroup 2 ↥X → InU0 M B → B ≤ X → X ≤ M)
    {B : Subgroup G} (hB : InU0 M B) {y : G} (hyM : y ∈ M) (hy2 : orderOf y = 2)
    (hyB : ∀ b ∈ B, b * y = y * b) : y ∈ derivedIn M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hny
  obtain ⟨n, φ, hφ⟩ := exists_hom_cyclic_of_not_mem_derived M hyM hny
  obtain ⟨hBM, hBel, -⟩ := hB.1
  obtain ⟨P, hBP, hyP⟩ := exists_sylow_two_ge_of_commute hBel hy2 hyB
  have hPM : (P : Subgroup G) ≤ M := hc P B P.isPGroup' hB hBP
  have hysq : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at this
  set M0 : Subgroup G := (MonoidHom.ker φ).map M.subtype with hM0
  have hM0mem : ∀ z : G, z ∈ M0 ↔ ∃ hz : z ∈ M, φ ⟨z, hz⟩ = 1 := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by simpa using hw⟩
    · rintro ⟨hz, h1⟩
      exact ⟨⟨z, hz⟩, h1, rfl⟩
  have hM0M : M0 ≤ M := fun z hz => ((hM0mem z).1 hz).1
  set Q : Subgroup G := (P : Subgroup G) ⊓ M0 with hQ
  have hQn : ∀ t ∈ (P : Subgroup G), ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    obtain ⟨hqM, hq1⟩ := (hM0mem q).1 hq.2
    have hz : t * q * t⁻¹ ∈ M := M.mul_mem (M.mul_mem (hPM ht) hqM) (M.inv_mem (hPM ht))
    refine ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ht hq.1) ((P : Subgroup G).inv_mem ht),
      (hM0mem _).2 ⟨hz, ?_⟩⟩
    have : φ ⟨t * q * t⁻¹, hz⟩ = φ ⟨t, hPM ht⟩ * φ ⟨q, hqM⟩ * (φ ⟨t, hPM ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [this, hq1, mul_one]
    exact mul_inv_cancel _
  have hcyc : ∃ b ∈ (P : Subgroup G), ∀ t ∈ (P : Subgroup G), ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
    set φP : ↥(P : Subgroup G) →* Multiplicative (ZMod n) :=
      φ.comp (Subgroup.inclusion hPM) with hφP
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥φP.range)
    obtain ⟨b', hb'⟩ := g.2
    refine ⟨(b' : G), b'.2, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨φP ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩⟩)
    have hk' : (φP b') ^ k = φP ⟨t, ht⟩ := by
      rw [hb']
      exact congrArg Subtype.val hk
    set e : ↥(P : Subgroup G) := (b' ^ k)⁻¹ * ⟨t, ht⟩ with he
    have hcoe : (e : G) = ((b' : G) ^ k)⁻¹ * t := by
      simp [he]
    have hmemP : (e : G) ∈ (P : Subgroup G) := e.2
    have hM : (e : G) ∈ M := hPM hmemP
    refine ⟨k, ?_⟩
    rw [← hcoe]
    refine ⟨hmemP, (hM0mem _).2 ⟨hM, ?_⟩⟩
    have : φ ⟨(e : G), hM⟩ = φP e := rfl
    rw [this, he, map_mul, map_inv, map_zpow, hk', inv_mul_cancel]
  have huQ : y ∉ Q := fun h => hφ (by
    obtain ⟨hz, h1⟩ := (hM0mem y).1 h.2
    exact h1)
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * y ^ (2 * k) * g ∈ (P : Subgroup G) →
      g⁻¹ * y ^ (2 * k) * g ∈ Q := by
    intro g k _
    have h1 : y ^ (2 * k) = 1 := by
      rw [pow_mul, pow_two, hysq, one_pow]
    rw [h1, mul_one, inv_mul_cancel]
    exact Q.one_mem
  have hfus : ∀ g : G, g⁻¹ * y * g ∈ (P : Subgroup G) → IsExtremalIn 2 (P : Subgroup G) (g⁻¹ * y * g) →
      y⁻¹ * (g⁻¹ * y * g) ∈ Q := by
    intro g hgP hext
    have hS : IsSylowOf 2 ((P : Subgroup G) ⊓ centralizer ({g⁻¹ * y * g} : Set G))
        (centralizer ({g⁻¹ * y * g} : Set G)) := isSylowOf_iff.2 hext
    obtain ⟨m, hm, hmy⟩ := prop92 h2 ⟨g⁻¹, by group⟩ hB hyB hS (inf_le_left.trans hPM)
    have hy'M : g⁻¹ * y * g ∈ M := hPM hgP
    have hz : y⁻¹ * (g⁻¹ * y * g) ∈ M := M.mul_mem (M.inv_mem hyM) hy'M
    refine ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hyP) hgP, (hM0mem _).2 ⟨hz, ?_⟩⟩
    have hφy' : φ ⟨g⁻¹ * y * g, hy'M⟩ = φ ⟨y, hyM⟩ := by
      have e : (⟨g⁻¹ * y * g, hy'M⟩ : ↥M) = ⟨m, hm⟩ * ⟨y, hyM⟩ * ⟨m, hm⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hmy.symm
      rw [e, map_mul, map_mul, map_inv, mul_comm (φ ⟨m, hm⟩) (φ ⟨y, hyM⟩), mul_assoc,
        mul_inv_cancel, mul_one]
    have e2 : (⟨y⁻¹ * (g⁻¹ * y * g), hz⟩ : ↥M) = ⟨y, hyM⟩⁻¹ * ⟨g⁻¹ * y * g, hy'M⟩ := rfl
    rw [e2, map_mul, map_inv, hφy', inv_mul_cancel]
  have hc : ∀ g : G, g⁻¹ * y * g ∈ (P : Subgroup G) →
      IsExtremalIn 2 (P : Subgroup G) (g⁻¹ * y * g) →
        g⁻¹ * y * g ∈ Q ∨ y⁻¹ * (g⁻¹ * y * g) ∈ Q :=
    fun g h1 h2' => Or.inr (hfus g h1 h2')
  rcases thompson_transfer_1515 (p := 2) P.isPGroup' P.not_dvd_index hQn
      hcyc hyP huQ hb hc with ⟨N, hN, hcycN, -, hyN⟩ | ⟨g, hgQ, hgext, -⟩
  ·
    rcases hG.eq_bot_or_eq_top_of_normal N with h0 | h0
    · subst h0
      have hcyc' : IsCyclic G :=
        isCyclic_of_surjective (QuotientGroup.quotientBot (G := G)).toMonoidHom
          (QuotientGroup.quotientBot (G := G)).surjective
      obtain ⟨a, b, hab⟩ := hnab
      let _ := IsCyclic.commGroup (α := G)
      exact hab (mul_comm a b)
    · exact hyN (h0 ▸ Subgroup.mem_top y)
  · have h1 := hfus g hgQ.1 hgext
    have h2' : y ∈ Q := by
      have e : y = (g⁻¹ * y * g) * (y⁻¹ * (g⁻¹ * y * g))⁻¹ := by group
      rw [e]
      exact Q.mul_mem hgQ (Q.inv_mem h1)
    exact huQ h2'


theorem not_mem_commutator_of_swap {M Q : Type} [Group M] [Finite M] [Group Q]
    (ψ : M →* Q) (L₁ L₂ : Subgroup Q)
    (hinv : ∀ m : M, (L₁.map (MulAut.conj (ψ m)).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj (ψ m)).toMonoidHom = L₂))
    (hne : L₁ ≠ L₂) {x : M} (hx : L₁.map (MulAut.conj (ψ x)).toMonoidHom = L₂) :
    x ∉ commutator M := by
  classical
  let _ : MulAction M (Subgroup Q) :=
    MulAction.compHom (Subgroup Q) ((MulAut.conj : Q →* MulAut Q).comp ψ)
  have hsmul : ∀ (m : M) (L : Subgroup Q), m • L = L.map (MulAut.conj (ψ m)).toMonoidHom :=
    fun m L => toSubmonoid_inj.mp rfl
  have hxS : x ∉ stabilizer M L₁ := by
    intro h
    rw [mem_stabilizer_iff, hsmul, hx] at h
    exact hne h.symm
  have horb : Nat.card (orbit M L₁) ≤ 2 := by
    have hsub : (orbit M L₁ : Set (Subgroup Q)) ⊆ {L₁, L₂} := by
      rintro _ ⟨m, rfl⟩
      rcases hinv m with h | h
      · exact Or.inl (by simpa [hsmul] using h)
      · exact Or.inr (by simpa [hsmul] using h)
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair hne).le
  have hidx : (stabilizer M L₁).index ≤ 2 := by
    rw [MulAction.index_stabilizer]; exact horb
  have hidx2 : (stabilizer M L₁).index = 2 := by
    have h0 : (stabilizer M L₁).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (stabilizer M L₁).index ≠ 1 := fun h =>
      hxS (Subgroup.index_eq_one.1 h ▸ Subgroup.mem_top x)
    omega
  have hn : (stabilizer M L₁).Normal := Subgroup.normal_of_index_eq_two hidx2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (M ⧸ stabilizer M L₁) = 2 := hidx2
  have hcyc : IsCyclic (M ⧸ stabilizer M L₁) := isCyclic_of_prime_card hcard
  have hcomm : commutator M ≤ stabilizer M L₁ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g _ h _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    exact (map_commutatorElement (QuotientGroup.mk' (stabilizer M L₁)) g h).trans
      (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' _ _))
  exact fun h => hxS (hcomm h)



theorem stage2Cor2_proved : Stage2Cor2Stmt := by
  intro G _ _ x K A M P Q H hset hc1 h2
  have hG : IsSimpleGroup G := hset.hyp.simple
  have hnab := hset.hyp.nonab
  obtain ⟨hAx, hAel, hAcard, -⟩ := hset.src
  have hx2 : orderOf x = 2 := hset.pair.1.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hset.pair.1.1.1.2.2.1
  have hr3 : pRank 2 ↥A = 3 := by
    have := hAel
    exact pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAe3 : IsE 3 ⊤ A := ⟨le_top, hAel, hr3.ge⟩
  have hbal := hset.reg.1
  have hAM : A ≤ M :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2
      ⟨le_rfl, hAel, by omega⟩).trans hset.le_M)
  have hU0 : InU0 M A := ⟨⟨hAM, hAel, by omega⟩, Or.inr hr3, by
    rw [hr3]
    exact (gammaK_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2).trans hset.le_M⟩
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxP : x ∈ P := by
    obtain ⟨S, hS⟩ := hset.sylowP
    have hcent : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈
        Subgroup.center ↥(centralizer ({x} : Set G)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : G) ∈ centralizer ({x} : Set G) := g.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hN : (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))).Normal :=
      normal_of_le_center (zpowers_le.2 hcent)
    have hx'2 : orderOf (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [← orderOf_injective (centralizer ({x} : Set G)).subtype
        (centralizer ({x} : Set G)).subtype_injective ⟨x, hxC⟩]
      exact hx2
    have hp : IsPGroup 2 (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx'2, pow_one]
    have hle := IsPGroup.le_sylow_of_normal hp S
    rw [← hS]
    exact ⟨⟨x, hxC⟩, hle (mem_zpowers _), rfl⟩
  have hxM : x ∈ M := hc1.Q_le (hset.Q_eq ▸ ⟨hxP, mem_CxK_self hKC⟩)
  have hc : ∀ X B : Subgroup G, IsPGroup 2 ↥X → InU0 M B → B ≤ X → X ≤ M :=
    fun X B => cor2_c h2 X B
  have hdA : ∀ a ∈ A, a ∈ derivedIn M := by
    intro a ha
    by_cases h1 : a = 1
    · rw [h1]; exact (derivedIn M).one_mem
    · obtain ⟨hcomm, hsq⟩ := CFSG.GH74.GLS.C3.Layer1.Back.forall_of_isElementaryAbelian hAel
      have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hsq a ha) h1
      exact prop93 hG hnab h2 hc hU0 (hAM ha) ha2 (fun b hb => hcomm b hb a ha)
  have hdx : x ∈ derivedIn M :=
    prop93 hG hnab h2 hc hU0 hxM hx2
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.1 (hAx hb))
  have hd : A ⊔ zpowers x ≤ derivedIn M ∧
      ∀ y ∈ M ⊓ centralizer (A : Set G), orderOf y = 2 → y ∈ derivedIn M :=
    ⟨sup_le (fun a ha => hdA a ha) (zpowers_le.2 hdx), fun y hy hy2 =>
      prop93 hG hnab h2 hc hU0 hy.1 hy2 (fun b hb => Subgroup.mem_centralizer_iff.1 hy.2 b hb)⟩
  have he : barIn M H = barIn M K ∨
      (barIn M H = generalizedFitting (Mbar M) ∧ IsSimpleGroup ↥(barIn M H)) := by
    rcases hc1.H_tri with h | h | ⟨hF, hxM', L₁, L₂, hL₁, hL₂, hne, -, -, hHL, hswap, hcomp⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      let ψ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)
      have hinv : ∀ m : ↥M, L₁.map (MulAut.conj (ψ m)).toMonoidHom = L₁ ∨
          L₁.map (MulAut.conj (ψ m)).toMonoidHom = L₂ := fun m =>
        hcomp _ (CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent
          (MulAut.conj (ψ m)) hL₁)
      have hnot : (⟨x, hxM⟩ : ↥M) ∉ commutator ↥M :=
        not_mem_commutator_of_swap ψ L₁ L₂ hinv hne (x := ⟨x, hxM⟩) hswap
      apply hnot
      obtain ⟨z, hz, hzx⟩ := hdx
      have : z = ⟨x, hxM⟩ := Subtype.ext hzx
      rwa [this] at hz
  exact ⟨cor2_a h2, cor2_b h2, cor2_c h2, hd, he⟩

end CFSG.GH74.Generic.BProg
