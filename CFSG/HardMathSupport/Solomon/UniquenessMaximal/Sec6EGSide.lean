module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGModel
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGSideFuse
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGSideFaith

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Basic

variable {G : Type*} [Group G] {B : Subgroup G}

theorem mem_autIn' {X : Subgroup G} {w : MulAut ↥B} :
    w ∈ autIn B X ↔ ∃ n : Subgroup.normalizer (B : Set G), (n : G) ∈ X ∧
      B.normalizerMonoidHom n = w :=
  Iff.rfl

theorem mem_autIn {X : Subgroup G} {w : MulAut ↥B} :
    w ∈ autIn B X ↔ ∃ g ∈ X ⊓ Subgroup.normalizer (B : Set G),
      ∀ y : ↥B, (w y : G) = g * y * g⁻¹ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, ⟨hn, n.2⟩, fun y => rfl⟩
  · rintro ⟨g, ⟨hgX, hgN⟩, h⟩
    refine ⟨⟨g, hgN⟩, hgX, ?_⟩
    ext y
    exact (h y).symm

theorem autIn_mono {X Y : Subgroup G} (h : X ≤ Y) : autIn B X ≤ autIn B Y := by
  rintro w ⟨n, hn, rfl⟩
  exact ⟨n, h hn, rfl⟩

theorem mem_inB {X : Subgroup G} {x : ↥B} : x ∈ inB B X ↔ (x : G) ∈ X := Iff.rfl

theorem elemAbelian_comm {E : Subgroup G} (h : IsElemAbelian 3 E) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (isMulCommutative_iff.1 h.1 ⟨x, hx⟩ ⟨y, hy⟩)

theorem elemAbelian_of {E : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (he : ∀ x ∈ E, x ^ 3 = 1) : IsElemAbelian 3 E :=
  ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hc a a.2 b b.2), he⟩

variable [Finite G]

theorem mem_normalizer_zpowers {g a : G} (h : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  rcases h with h | h
  · rw [h]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) z
  · rw [h]; exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) z

theorem mem_normalizer_iSup_of_set (S : Set G) (P : G → Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer (⨆ g ∈ S, (P g : Set G))) :
    n ∈ Subgroup.normalizer ((⨆ g ∈ S, P g : Subgroup G) : Set G) := by
  have : Finite ((⨆ g ∈ S, P g : Subgroup G) : Set G) := Subtype.finite
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hle : (⨆ g ∈ S, P g : Subgroup G) ≤
      (⨆ g ∈ S, P g : Subgroup G).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun g hg u hu => ?_
    have hu' : u ∈ (⨆ g ∈ S, (P g : Set G)) := by
      simp only [Set.iSup_eq_iUnion, Set.mem_iUnion]
      exact ⟨g, hg, hu⟩
    have h1 := (Subgroup.mem_set_normalizer_iff.1 hn u).1 hu'
    simp only [Set.iSup_eq_iUnion, Set.mem_iUnion] at h1
    obtain ⟨g', hg', h2⟩ := h1
    exact (le_iSup₂_of_le g' hg' le_rfl : P g' ≤ (⨆ g ∈ S, P g : Subgroup G)) h2
  exact hle hx

omit [Finite G] in
theorem jOf_le (L A : Subgroup G) : jLayerOf L A ≤ L ⊓ Subgroup.centralizer (A : Set G) :=
  sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem jOf_le_kOf (L A : Subgroup G) (x : G) : jLayerOf L A ≤ kOf L A x := by
  refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
  intro z hz
  exact ⟨z, hz, by simp⟩

end Basic

section Core

variable {G : Type} [Group G] [Finite G] {m : ℕ}

theorem normalizer_zpowers_le_kOf (h515 : Lemma515) (hS : GLStanding G m 3)
    (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤
      Subgroup.normalizer ((kOf L A a : Subgroup G) : Set G) :=
  fun _ hg => h515 G m hS hC B hB b L A hw a ha ha1 hg

theorem B_le_normalizer_kOf (h515 : Lemma515) (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    B ≤ Subgroup.normalizer ((kOf L A a : Subgroup G) : Set G) := by
  have hAB : A ≤ B := hw.2.2.2.2.2.1.2.1.1
  have hcomm := elemAbelian_comm hB.1.1
  intro y hy
  apply normalizer_zpowers_le_kOf h515 hS hC hB hw ha ha1
  apply mem_normalizer_zpowers
  left
  have := hcomm y hy a (hAB ha)
  rw [this]; group

theorem kKey (h30 : Input30_2) (hk : InputKType) (h515 : Lemma515)
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    (∀ y ∈ B, y ∈ kOf L A a → y ∈ B ⊓ L) ∧
    (∀ k ∈ kOf L A a, k ∈ Subgroup.normalizer (B : Set G) → (∀ f ∈ B ⊓ L, k * f * k⁻¹ = f) →
      ∀ y ∈ B, k * y * k⁻¹ = y) := by
  have hBnK := B_le_normalizer_kOf h515 hS hC hB hw ha ha1
  have hKtype := hk G m hS hC B hB b L A hw a ha ha1
  have h30K := h30 ↥(kOf L A a) hKtype
  obtain ⟨hbB, hb1, hL, hbal, hty, ⟨hF, hA, hbA, hfld, hJ, q8, hq8⟩, hx⟩ := hw
  have hBcomm := elemAbelian_comm hB.1.1
  have hBexp : ∀ x ∈ B, x ^ 3 = 1 := hB.1.1.2
  have hFK : B ⊓ L ≤ kOf L A a := le_trans hJ (jOf_le_kOf L A a)
  have hFexp : ∀ x ∈ B ⊓ L, x ^ 3 = 1 := fun x hx => hBexp x hx.1
  have hFcomm : ∀ x ∈ B ⊓ L, ∀ y ∈ B ⊓ L, x * y = y * x := fun x hx y hy => hBcomm x hx.1 y hy.1
  have hF'el : IsElemAbelian 3 ((B ⊓ L).subgroupOf (kOf L A a)) :=
    elemAbelian_of (fun x hx y hy => Subtype.ext (hFcomm x hx y hy))
      (fun x hx => Subtype.ext (hFexp x hx))
  have hEel : IsElemAbelian 3 (B.subgroupOf (kOf L A a)) :=
    elemAbelian_of (fun x hx y hy => Subtype.ext (hBcomm x hx y hy))
      (fun x hx => Subtype.ext (hBexp x hx))
  have hcard9 : Nat.card ((B ⊓ L).subgroupOf (kOf L A a)) = 9 := by
    rw [← hF]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv
  have hle : (B ⊓ L).subgroupOf (kOf L A a) ≤ B.subgroupOf (kOf L A a) := fun x hx => hx.1
  have hEF : (B ⊓ L).subgroupOf (kOf L A a) = B.subgroupOf (kOf L A a) :=
    Subgroup.eq_of_le_of_card_ge hle (by have := h30K.1 _ hEel; omega)
  have hBK : ∀ y ∈ B, y ∈ kOf L A a → y ∈ B ⊓ L := by
    intro y hy hyK
    have : (⟨y, hyK⟩ : ↥(kOf L A a)) ∈ (B ⊓ L).subgroupOf (kOf L A a) := by
      rw [hEF]; exact hy
    exact this
  refine ⟨hBK, ?_⟩
  intro k hkK hkN hkF y hy
  have hfused : ∀ x ∈ (B ⊓ L).subgroupOf (kOf L A a), x ≠ 1 →
      ∀ y ∈ (B ⊓ L).subgroupOf (kOf L A a), y ≠ 1 → ∃ g : ↥(kOf L A a), g * x * g⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨n, hn, hnxy⟩ := fuse_of_q8 (jLayerOf L A) (B ⊓ L) hFcomm hFexp hF q8 hq8 x hx
      (fun h => hx1 (Subtype.ext h)) y hy (fun h => hy1 (Subtype.ext h))
    exact ⟨⟨n, jOf_le_kOf L A a hn.1⟩, Subtype.ext hnxy⟩
  refine faithful_core B (kOf L A a) (B ⊓ L) hBcomm inf_le_left hBK
    (fun y hy z hz => (Subgroup.mem_normalizer_iff.1 (hBnK hy) z).1 hz) hFexp ?_ hkK
    (fun y hy => (Subgroup.mem_normalizer_iff.1 hkN y).1 hy) hkF y hy
  intro P hP hPc hFP
  exact h30K.2 _ hF'el hcard9 hfused P hP hPc hFP

theorem sideK_S (h30 : Input30_2) (hk : InputKType) (h515 : Lemma515)
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {a : ↥B} (ha : a ∈ inB B A) (ha1 : a ≠ 1) :
    ∃ S : Subgroup (MulAut ↥B), S ≤ autIn B ⊤ ∧ autIn B (jLayerOf L A) ≤ S ∧
      (∀ s ∈ S, ∀ f ∈ inB B (B ⊓ L), s f ∈ inB B (B ⊓ L)) ∧
      (∀ s ∈ S, (∀ f ∈ inB B (B ⊓ L), s f = f) → s = 1) ∧
      ∀ w ∈ autIn B ⊤, (w a = a ∨ w a = a⁻¹) → ∀ s ∈ S, w * s * w⁻¹ ∈ S := by
  have haA : (a : G) ∈ A := ha
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨hBK, hfaith⟩ := kKey h30 hk h515 hS hC hB hw haA ha1'
  have hJ : B ⊓ L ≤ kOf L A a :=
    le_trans hw.2.2.2.2.2.1.2.2.2.2.1 (jOf_le_kOf L A a)
  refine ⟨autIn B (kOf L A a), autIn_mono le_top, autIn_mono (jOf_le_kOf L A a), ?_, ?_, ?_⟩
  · intro s hs f hf
    obtain ⟨k, ⟨hkK, hkN⟩, hsk⟩ := mem_autIn.1 hs
    have hf' : (f : G) ∈ B ⊓ L := hf
    refine ⟨(s f).2, ?_⟩
    apply (hBK _ (s f).2 _).2
    rw [hsk f]
    exact (kOf L A a).mul_mem ((kOf L A a).mul_mem hkK (hJ hf')) ((kOf L A a).inv_mem hkK)
  · intro s hs hsF
    obtain ⟨k, ⟨hkK, hkN⟩, hsk⟩ := mem_autIn.1 hs
    ext y
    have := hfaith k hkK hkN (fun f hf => by
      have := hsF ⟨f, hf.1⟩ hf
      rw [← hsk ⟨f, hf.1⟩]
      exact congrArg Subtype.val this) y y.2
    rw [hsk y]
    exact this
  · intro w hw' hwa s hs
    obtain ⟨nw, -, rfl⟩ := mem_autIn'.1 hw'
    obtain ⟨ns, hns, rfl⟩ := mem_autIn'.1 hs
    have hnwa : (nw : G) ∈ Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) := by
      apply mem_normalizer_zpowers
      rcases hwa with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    have hnwK := normalizer_zpowers_le_kOf h515 hS hC hB hw haA ha1' hnwa
    refine mem_autIn'.2 ⟨nw * ns * nw⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.1 hnwK ns).1 hns
    simpa using this

end Core

section Main

variable {G : Type} [Group G] [Finite G] {m : ℕ}

omit [Finite G] in
theorem exists_ne_one_of_card {A : Subgroup G} (h : Nat.card A = 3 ^ 2) : ∃ x ∈ A, x ≠ 1 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hA : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
  rw [hA, Subgroup.card_bot] at h
  norm_num at h

theorem gSideK_of_inputs (h30 : Input30_2) (hk : InputKType) (h515 : Lemma515)
    {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {Q : Subgroup (MulAut ↥B)} (hQ : Q ≤ autIn B (jLayerOf L A))
    (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) :
    GSideK B (inB B A) (inB B (B ⊓ L)) Q := by
  have _ := hQ8
  have hw' := hw
  obtain ⟨-, -, -, -, -, ⟨-, hA, -, -, -, -⟩, -⟩ := hw'
  obtain ⟨x, hxA, hx1⟩ := exists_ne_one_of_card hA.2.2
  have hxB : x ∈ B := hA.1 hxA
  have hQact : ∀ q ∈ Q, ∃ g ∈ jLayerOf L A, ∀ y : ↥B, (q y : G) = g * y * g⁻¹ := by
    intro q hq
    obtain ⟨g, ⟨hg, -⟩, h⟩ := mem_autIn.1 (hQ hq)
    exact ⟨g, hg, h⟩
  have hside := fun (a : ↥B) (ha : a ∈ inB B A) (ha1 : a ≠ 1) =>
    sideK_S h30 hk h515 hS hC hB hw ha ha1
  refine ⟨hQ.trans (autIn_mono le_top), ?_, ?_, ?_, ?_⟩
  · intro q hq a ha
    obtain ⟨g, hg, h⟩ := hQact q hq
    apply Subtype.ext
    rw [h a]
    have hc := Subgroup.mem_centralizer_iff.1 (jOf_le L A hg).2 a ha
    rw [← hc]
    simp
  · intro q hq f hf
    obtain ⟨g, hg, h⟩ := hQact q hq
    have hL : (q f : G) ∈ L := by
      rw [h f]
      exact L.mul_mem (L.mul_mem (jOf_le L A hg).1 (hf : (f : G) ∈ B ⊓ L).2)
        (L.inv_mem (jOf_le L A hg).1)
    exact mem_inB.2 ⟨(q f).2, hL⟩
  · intro q hq hqF
    obtain ⟨S, -, hJS, -, hfa, -⟩ := hside ⟨x, hxB⟩ hxA (fun h => hx1 (congrArg Subtype.val h))
    exact hfa q (hJS (hQ hq)) hqF
  · intro a ha ha1
    obtain ⟨S, hSW, hJS, hF1, hfa, hnorm⟩ := hside a ha ha1
    exact ⟨S, hSW, hQ.trans hJS, hF1, hfa, hnorm⟩

theorem gSideJ_of_inputs (h30 : Input30_2) (hk : InputKType) (h515 : Lemma515)
    (hJ : InputJNormalA)
    {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) {Q : Subgroup (MulAut ↥B)} (hQ : Q ≤ autIn B (jLayerOf L A))
    (hQ8 : Nonempty (Q ≃* QuaternionGroup 2)) :
    GSideJ B (inB B A) (inB B (B ⊓ L)) Q := by
  have _ := hQ8
  show ∃ S : Subgroup (MulAut ↥B), S ≤ autIn B ⊤ ∧ Q ≤ S ∧
    (∀ s ∈ S, ∀ f ∈ inB B (B ⊓ L), s f ∈ inB B (B ⊓ L)) ∧
    (∀ s ∈ S, (∀ f ∈ inB B (B ⊓ L), s f = f) → s = 1) ∧
    ∀ w ∈ autIn B ⊤, (∀ a ∈ inB B A, w a ∈ inB B A) → ∀ s ∈ S, w * s * w⁻¹ ∈ S
  have hw' := hw
  obtain ⟨-, -, -, -, -, ⟨-, hA, -, -, -, -⟩, -⟩ := hw'
  obtain ⟨x, hxA, hx1⟩ := exists_ne_one_of_card hA.2.2
  have hxB : x ∈ B := hA.1 hxA
  obtain ⟨S₀, -, hJS₀, hF1, hfa, -⟩ :=
    sideK_S h30 hk h515 hS hC hB hw (a := ⟨x, hxB⟩) hxA (fun h => hx1 (congrArg Subtype.val h))
  refine ⟨autIn B (jLayerOf L A), autIn_mono le_top, hQ, fun s hs f hf => hF1 s (hJS₀ hs) f hf,
    fun s hs hf => hfa s (hJS₀ hs) hf, ?_⟩
  intro w hw'' hwA s hs
  obtain ⟨nw, -, rfl⟩ := mem_autIn'.1 hw''
  obtain ⟨ns, hns, rfl⟩ := mem_autIn'.1 hs
  have hnA : (nw : G) ∈ Subgroup.normalizer (A : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    exact hwA ⟨y, hA.1 hy⟩ hy
  have hnJ := hJ G m hS hC B hB b L A hw hnA
  refine mem_autIn'.2 ⟨nw * ns * nw⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 hnJ ns).1 hns
  simpa using this

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
