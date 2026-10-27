module

public import CFSG.Open.GLBDefs
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem sSup_normal_subgroupOf {G : Type*} [Group G] {H : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ N ∈ S, N ≤ H ∧ (N.subgroupOf H).Normal) :
    sSup S ≤ H ∧ ((sSup S).subgroupOf H).Normal := by
  have hle : sSup S ≤ H := sSup_le fun N hN => (hS N hN).1
  refine ⟨hle, ?_⟩
  let T : Subgroup G :=
    { carrier := {x | ∀ g ∈ H, g * x * g⁻¹ ∈ sSup S}
      one_mem' := fun g _ => by simp
      mul_mem' := fun {a b} ha hb g hg => by
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]
        exact mul_mem (ha g hg) (hb g hg)
      inv_mem' := fun {a} ha g hg => by
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem (ha g hg) }
  have hT : sSup S ≤ T := by
    refine sSup_le fun N hN => ?_
    intro x hx
    show ∀ g ∈ H, g * x * g⁻¹ ∈ sSup S
    intro g hg
    obtain ⟨hNH, hNn⟩ := hS N hN
    have h := hNn.conj_mem ⟨x, hNH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
    exact le_sSup hN (Subgroup.mem_subgroupOf.mp h)
  constructor
  intro n hn g
  have hn' : (n : G) ∈ sSup S := Subgroup.mem_subgroupOf.mp hn
  have hT2 : ∀ g ∈ H, g * (n : G) * g⁻¹ ∈ sSup S := hT hn'
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hT2 (g : G) g.2)

theorem glbPrimeCore_subgroupOf_eq {G : Type*} [Group G] (p : ℕ) (C : Subgroup G) :
    (CFSG.Open.GLBPrimeCore p C).subgroupOf C = CFSG.pPrimeCore p C := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have key : CFSG.Open.GLBPrimeCore p C ≤ (CFSG.pPrimeCore p C).map C.subtype := by
      apply sSup_le
      intro N hN
      obtain ⟨hNC, hNn, hcop⟩ := hN
      intro z hz
      have hzC : z ∈ C := hNC hz
      have hcard : Nat.card (N.subgroupOf C) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
      have hle : N.subgroupOf C ≤ CFSG.pPrimeCore p C := by
        unfold CFSG.pPrimeCore
        exact le_sSup ⟨hNn, by rw [hcard]; exact hcop⟩
      have hw : (⟨z, hzC⟩ : C) ∈ N.subgroupOf C := Subgroup.mem_subgroupOf.mpr hz
      exact Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, hle hw, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (key hx)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  · unfold CFSG.pPrimeCore
    apply sSup_le
    rintro K ⟨hK, hcop⟩
    have hNK : (K.map C.subtype).subgroupOf C = K := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hxy : y = x := Subtype.ext hyx
        rw [← hxy]
        exact hy
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hcardK : Nat.card (K.map C.subtype) = Nat.card K :=
      (Nat.card_congr (Subgroup.equivMapOfInjective K C.subtype Subtype.val_injective).toEquiv).symm
    have hNle : K.map C.subtype ≤ CFSG.Open.GLBPrimeCore p C := by
      unfold CFSG.Open.GLBPrimeCore CFSG.Open.relPPrimeCore
      refine le_sSup ⟨?_, ?_, ?_⟩
      · intro z hz
        obtain ⟨y, _, hyz⟩ := Subgroup.mem_map.mp hz
        rw [← hyz]
        exact y.2
      · rw [hNK]
        exact hK
      · rw [hcardK]
        exact hcop
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hNle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem subgroupOf_normal_of_conj {G : Type*} [Group G] {M X : Subgroup G}
    (h : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X) : (X.subgroupOf M).Normal := by
  constructor
  intro n hn g
  apply Subgroup.mem_subgroupOf.mpr
  have := h g g.2 n (Subgroup.mem_subgroupOf.mp hn)
  simpa using this

theorem eq_of_card_eq_of_isCyclic {X : Type*} [Group X] [IsCyclic X] [Finite X]
    {A B : Subgroup X} (h : Nat.card A = Nat.card B) : A = B :=
  IsCyclic.subgroup_eq_iff_card_eq.mpr h

theorem exists_card_three_le_of_isPGroup {G : Type*} [Group G] [Finite G] {D : Subgroup G}
    (hD : IsPGroup 3 D) (hD1 : D ≠ ⊥) : ∃ P₀ : Subgroup G, P₀ ≤ D ∧ Nat.card P₀ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfin : Finite D := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := D)).mp hD
  have hne : n ≠ 0 := by
    rintro rfl
    apply hD1
    have h1 : Nat.card D = 1 := by simpa using hn
    rw [Subgroup.eq_bot_iff_card]
    exact h1
  have h3 : 3 ∣ Nat.card D := by
    rw [hn]
    exact dvd_pow_self 3 hne
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3
  refine ⟨Subgroup.zpowers (g : G), ?_, ?_⟩
  · exact (Subgroup.zpowers_le).mpr g.2
  · rw [Nat.card_zpowers]
    rw [Subgroup.orderOf_coe, hg]

theorem card_map_mk_of_inf_eq_bot {X : Type*} [Group X] (A N : Subgroup X) [N.Normal]
    (h : A ⊓ N = ⊥) : Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  let f : A →* X ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : X) ∈ N := (QuotientGroup.eq_one_iff (x : X)).mp hx
    have hmem : (x : X) ∈ A ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrange : A.map (QuotientGroup.mk' N) = f.range := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
  rw [hrange]
  exact (Nat.card_congr (Equiv.ofInjective f hf)).symm

theorem exists_minimal_normal_ne_bot {X : Type*} [Group X] [Finite X] [Nontrivial X] :
    ∃ K : Subgroup X, K.Normal ∧ K ≠ ⊥ ∧
      ∀ K' : Subgroup X, K'.Normal → K' ≤ K → K' = ⊥ ∨ K' = K := by
  classical
  have htb : (⊤ : Subgroup X) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    have hxt : x ∈ (⊤ : Subgroup X) := Subgroup.mem_top x
    rw [h, Subgroup.mem_bot] at hxt
    exact hx hxt
  have hex : ∃ n : ℕ, ∃ K : Subgroup X, K.Normal ∧ K ≠ ⊥ ∧ Nat.card K = n :=
    ⟨_, ⊤, inferInstance, htb, rfl⟩
  obtain ⟨K, hKn, hKb, hKc⟩ := Nat.find_spec hex
  refine ⟨K, hKn, hKb, ?_⟩
  intro K' hK'n hK'K
  by_cases h' : K' = ⊥
  · exact Or.inl h'
  right
  by_contra hne
  have hlt : Nat.card K' < Nat.find hex := by
    rw [← hKc]
    rcases (Subgroup.card_le_of_le hK'K).lt_or_eq with hl | he
    · exact hl
    · exact absurd (Subgroup.eq_of_le_of_card_ge hK'K he.ge) hne
  exact Nat.find_min hex hlt ⟨K', hK'n, h', rfl⟩

theorem inf_eq_bot_of_isPGroup_coprime {X : Type*} [Group X] [Finite X] (S N : Subgroup X)
    (hS : IsPGroup 3 S) (hN : Nat.Coprime 3 (Nat.card N)) : S ⊓ N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := S)).mp hS
  have h1 : Nat.card (S ⊓ N : Subgroup X) ∣ Nat.card S :=
    Subgroup.card_dvd_of_le (inf_le_left : S ⊓ N ≤ S)
  have h2 : Nat.card (S ⊓ N : Subgroup X) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le (inf_le_right : S ⊓ N ≤ N)
  have hcop : Nat.Coprime (Nat.card (S ⊓ N : Subgroup X)) (Nat.card N) := by
    have h3 : Nat.Coprime (3 ^ n) (Nat.card N) := Nat.Coprime.pow_left n hN
    rw [← hn] at h3
    exact Nat.Coprime.coprime_dvd_left h1 h3
  have hone : Nat.card (S ⊓ N : Subgroup X) = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  rw [Subgroup.eq_bot_iff_card]
  exact hone

theorem index_map_mk_dvd {X : Type*} [Group X] (S N : Subgroup X) [N.Normal] :
    (S.map (QuotientGroup.mk' N)).index ∣ S.index :=
  Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective N)

theorem not_dvd_index_map_mk {X : Type*} [Group X] (S N : Subgroup X) [N.Normal]
    (h : ¬ 3 ∣ S.index) : ¬ 3 ∣ (S.map (QuotientGroup.mk' N)).index :=
  fun h' => h (dvd_trans h' (index_map_mk_dvd S N))

theorem isCyclic_map_of_isCyclic {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (S : Subgroup X) [IsCyclic S] : IsCyclic (S.map f) := by
  let g : S →* S.map f :=
    { toFun := fun s => ⟨f (s : X), Subgroup.mem_map_of_mem f s.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : X) (b : X)) }
  refine isCyclic_of_surjective g ?_
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem pCore_quotient_ne_bot {X : Type*} [Group X] [Finite X]
    (hX : CFSG.HallHigman.IsPSolvable 3 X) [Nontrivial (X ⧸ CFSG.pPrimeCore 3 X)] :
    CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal
  have hQ : CFSG.pPrimeCore 3 (X ⧸ CFSG.pPrimeCore 3 X) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hsepQ : CFSG.HallHigman.IsPiSeparable {q : Nat.Primes | q.val = 3}
      (X ⧸ CFSG.pPrimeCore 3 X) :=
    (CFSG.HallHigman.isPiSeparable_of_isPSolvable Nat.prime_three hX).quotient _
  obtain ⟨K, hKn, hKb, hKmin⟩ := exists_minimal_normal_ne_bot (X := X ⧸ CFSG.pPrimeCore 3 X)
  rcases hsepQ.minimal_normal hKb hKmin with h | h
  · have hpos : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    have hK3 : IsPGroup 3 K := by
      rw [IsPGroup.iff_card]
      refine ⟨(Nat.card K).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hpos ?_⟩
      intro d hd hdvd
      exact h ⟨d, hd⟩ hdvd
    intro hbot
    have hle : K ≤ CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X) := by
      unfold CFSG.pCore
      exact le_sSup ⟨hKn, hK3⟩
    rw [hbot] at hle
    exact hKb (le_bot_iff.mp hle)
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card K) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hdvd
      exact h ⟨3, Nat.prime_three⟩ hdvd rfl
    have hle : K ≤ CFSG.pPrimeCore 3 (X ⧸ CFSG.pPrimeCore 3 X) := by
      unfold CFSG.pPrimeCore
      exact le_sSup ⟨hKn, hcop⟩
    rw [hQ, le_bot_iff] at hle
    exact hKb hle

theorem eq_of_le_isCyclic_of_card_eq {Q : Type*} [Group Q] [Finite Q] {Y Z₁ Z₂ : Subgroup Q}
    [IsCyclic Y] (h₁ : Z₁ ≤ Y) (h₂ : Z₂ ≤ Y) (hc : Nat.card Z₁ = Nat.card Z₂) : Z₁ = Z₂ := by
  have hsub : Z₁.subgroupOf Y = Z₂.subgroupOf Y := by
    apply eq_of_card_eq_of_isCyclic
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv]
    exact hc
  have e₁ : (Z₁.subgroupOf Y).map Y.subtype = Z₁ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₁]
  have e₂ : (Z₂.subgroupOf Y).map Y.subtype = Z₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₂]
  rw [← e₁, ← e₂, hsub]

theorem pCore_le_image_of_index {X : Type*} [Group X] [Finite X] (S N : Subgroup X) [N.Normal]
    (hS : IsPGroup 3 S) (hSi : ¬ 3 ∣ S.index) :
    CFSG.pCore 3 (X ⧸ N) ≤ S.map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let syl : Sylow 3 (X ⧸ N) :=
    IsPGroup.toSylow (hS.map (QuotientGroup.mk' N)) (not_dvd_index_map_mk S N hSi)
  have hle : CFSG.pCore 3 (X ⧸ N) ≤ syl := IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup syl
  have hcoe : (syl : Subgroup (X ⧸ N)) = S.map (QuotientGroup.mk' N) :=
    IsPGroup.toSylow_coe _ _
  exact le_trans hle (le_of_eq hcoe)

theorem exists_unique_card_three_pCore_quotient {X : Type*} [Group X] [Finite X]
    (hX : CFSG.HallHigman.IsPSolvable 3 X) [Nontrivial (X ⧸ CFSG.pPrimeCore 3 X)]
    (S : Subgroup X) (hS : IsPGroup 3 S) (hSi : ¬ 3 ∣ S.index) [IsCyclic S] :
    ∃ Z : Subgroup (X ⧸ CFSG.pPrimeCore 3 X), Nat.card Z = 3 ∧
      Z ≤ CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X) ∧
      ∀ Z' : Subgroup (X ⧸ CFSG.pPrimeCore 3 X), Nat.card Z' = 3 →
        Z' ≤ CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X) → Z' = Z := by
  have : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal
  have hne := pCore_quotient_ne_bot hX
  have hPg : IsPGroup 3 (CFSG.pCore 3 (X ⧸ CFSG.pPrimeCore 3 X)) := CFSG.pCore_isPGroup
  obtain ⟨Z, hZle, hZc⟩ := exists_card_three_le_of_isPGroup hPg hne
  have hSbar : IsCyclic (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) :=
    isCyclic_map_of_isCyclic _ S
  have hpc := pCore_le_image_of_index S (CFSG.pPrimeCore 3 X) hS hSi
  refine ⟨Z, hZc, hZle, ?_⟩
  intro Z' hZ'c hZ'le
  exact eq_of_le_isCyclic_of_card_eq (Y := S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (le_trans hZ'le hpc) (le_trans hZle hpc) (hZ'c.trans hZc.symm)

theorem map_conj_eq_self {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) :
    C.map (MulAut.conj m).toMonoidHom = C := by
  apply le_antisymm
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have h := hCn.conj_mem ⟨x, hCM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.mp h
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨m⁻¹ * x * m, ?_, ?_⟩
    · have h := hCn.conj_mem ⟨x, hCM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m⁻¹, M.inv_mem hm⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · show m * (m⁻¹ * x * m) * m⁻¹ = x
      group

def conjEquiv {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) : C ≃* C :=
  (MulEquiv.subgroupMap (MulAut.conj m) C).trans (MulEquiv.subgroupCongr (map_conj_eq_self hCM hCn hm))

theorem conjEquiv_coe {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) (x : C) :
    ((conjEquiv hCM hCn hm x : C) : G) = m * (x : G) * m⁻¹ := by
  unfold conjEquiv
  rfl

theorem conjEquiv_pPrimeCore {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) :
    (CFSG.pPrimeCore 3 C).map (conjEquiv hCM hCn hm).toMonoidHom = CFSG.pPrimeCore 3 C :=
  CFSG.pPrimeCore_map_iso 3 (conjEquiv hCM hCn hm)

def conjQuot {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) :
    (C ⧸ CFSG.pPrimeCore 3 C) ≃* (C ⧸ CFSG.pPrimeCore 3 C) :=
  QuotientGroup.congr (CFSG.pPrimeCore 3 C) (CFSG.pPrimeCore 3 C) (conjEquiv hCM hCn hm)
    (conjEquiv_pPrimeCore hCM hCn hm)

theorem conjQuot_mk' {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) (x : C) :
    conjQuot hCM hCn hm (QuotientGroup.mk' (CFSG.pPrimeCore 3 C) x) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 C) (conjEquiv hCM hCn hm x) :=
  QuotientGroup.congr_mk' _ _ _ _ _

theorem map_conjQuot_eq {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M)
    (Z : Subgroup (C ⧸ CFSG.pPrimeCore 3 C))
    (hZc : Nat.card Z = 3) (hZle : Z ≤ CFSG.pCore 3 (C ⧸ CFSG.pPrimeCore 3 C))
    (hunique : ∀ Z' : Subgroup (C ⧸ CFSG.pPrimeCore 3 C), Nat.card Z' = 3 →
      Z' ≤ CFSG.pCore 3 (C ⧸ CFSG.pPrimeCore 3 C) → Z' = Z) :
    Z.map (conjQuot hCM hCn hm).toMonoidHom = Z := by
  apply hunique
  · have hinj : Function.Injective (conjQuot hCM hCn hm).toMonoidHom :=
      (conjQuot hCM hCn hm).injective
    rw [Subgroup.card_map_of_injective hinj]
    exact hZc
  · calc Z.map (conjQuot hCM hCn hm).toMonoidHom
        ≤ (CFSG.pCore 3 (C ⧸ CFSG.pPrimeCore 3 C)).map (conjQuot hCM hCn hm).toMonoidHom :=
          Subgroup.map_mono hZle
      _ = CFSG.pCore 3 (C ⧸ CFSG.pPrimeCore 3 C) :=
          CFSG.pCore_map_iso 3 (conjQuot hCM hCn hm)

theorem isCyclic_of_map_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (S : Subgroup X) [IsCyclic (S.map f)] : IsCyclic S :=
  (MulEquiv.isCyclic (Subgroup.equivMapOfInjective S f hf)).mpr inferInstance

theorem pPrimeCore_ne_top_of_isPGroup {X : Type*} [Group X] [Finite X] (S : Subgroup X)
    (hS : IsPGroup 3 S) (hS1 : S ≠ ⊥) : CFSG.pPrimeCore 3 X ≠ ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro htop
  have hc : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 X)) := CFSG.pPrimeCore_coprime_card
  rw [htop, Subgroup.card_top, Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at hc
  apply hc
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := S)).mp hS
  have hne : n ≠ 0 := by
    rintro rfl
    apply hS1
    have h1 : Nat.card S = 1 := by simpa using hn
    rw [Subgroup.eq_bot_iff_card]
    exact h1
  have h3 : 3 ∣ Nat.card S := by
    rw [hn]
    exact dvd_pow_self 3 hne
  exact dvd_trans h3 (Subgroup.card_subgroup_dvd_card S)

theorem map_mk_inf_comap_eq {X : Type*} [Group X] (S N : Subgroup X) [N.Normal]
    (Z : Subgroup (X ⧸ N)) (hZ : Z ≤ S.map (QuotientGroup.mk' N)) :
    (S ⊓ Z.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = Z := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).2
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp (hZ hz)
    exact Subgroup.mem_map.mpr ⟨s, Subgroup.mem_inf.mpr ⟨hs, Subgroup.mem_comap.mpr hz⟩, rfl⟩

theorem card_inf_comap_eq_three {X : Type*} [Group X] [Finite X] (S : Subgroup X)
    (hS : IsPGroup 3 S) (Z : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) (hZc : Nat.card Z = 3)
    (hZ : Z ≤ S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) :
    Nat.card ↥(S ⊓ Z.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = 3 := by
  have hSb : S ⊓ CFSG.pPrimeCore 3 X = ⊥ :=
    inf_eq_bot_of_isPGroup_coprime S _ hS CFSG.pPrimeCore_coprime_card
  have hbot : (S ⊓ Z.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ⊓ CFSG.pPrimeCore 3 X = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans hSb.le)
  have h := card_map_mk_of_inf_eq_bot _ (CFSG.pPrimeCore 3 X) hbot
  rw [map_mk_inf_comap_eq S _ Z hZ, hZc] at h
  exact h.symm

theorem conj_mem_pPrimeCore_map {G : Type*} [Group G] {M C : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M) (y : C)
    (hy : y ∈ CFSG.pPrimeCore 3 C) :
    m * (y : G) * m⁻¹ ∈ (CFSG.pPrimeCore 3 C).map C.subtype := by
  have h1 : conjEquiv hCM hCn hm y ∈ CFSG.pPrimeCore 3 C := by
    rw [← conjEquiv_pPrimeCore hCM hCn hm]
    exact Subgroup.mem_map_of_mem _ hy
  rw [← conjEquiv_coe hCM hCn hm y]
  exact Subgroup.mem_map_of_mem C.subtype h1

theorem exists_normal_order_three_of_cyclic_sylow
    {G : Type*} [Group G] [Finite G] {M C D : Subgroup G} (hCM : C ≤ M)
    (hCn : (C.subgroupOf M).Normal) (hCs : CFSG.HallHigman.IsPSolvable 3 ↥C)
    (hD : ∃ S : Sylow 3 ↥C, (S : Subgroup ↥C).map C.subtype = D)
    (hDc : IsCyclic ↥D) (hD1 : D ≠ ⊥) :
    ∃ P₀ : Subgroup G, P₀ ≤ D ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M).subgroupOf M).Normal := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S0, hS0D⟩ := hD
  set S : Subgroup ↥C := (S0 : Subgroup ↥C) with hSdef
  have hSp : IsPGroup 3 S := S0.isPGroup'
  have hSi : ¬ 3 ∣ S.index := Sylow.not_dvd_index S0
  have hSne : S ≠ ⊥ := by
    intro h
    apply hD1
    rw [← hS0D, h, Subgroup.map_bot]
  have hSc : IsCyclic S := by
    have hm : IsCyclic (S.map C.subtype) := by
      rw [hS0D]
      exact hDc
    exact isCyclic_of_map_injective C.subtype Subtype.val_injective S
  have hnt : Nontrivial (↥C ⧸ CFSG.pPrimeCore 3 ↥C) := by
    rw [QuotientGroup.nontrivial_iff]
    exact pPrimeCore_ne_top_of_isPGroup S hSp hSne
  obtain ⟨Z, hZc, hZle, hunique⟩ := exists_unique_card_three_pCore_quotient hCs S hSp hSi
  have hZS : Z ≤ S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) :=
    le_trans hZle (pCore_le_image_of_index S (CFSG.pPrimeCore 3 ↥C) hSp hSi)
  set P0 : Subgroup ↥C := S ⊓ Z.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) with hP0def
  have hP0map : P0.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) = Z :=
    map_mk_inf_comap_eq S _ Z hZS
  have hP0c : Nat.card P0 = 3 := card_inf_comap_eq_three S hSp Z hZc hZS
  have hP0S : P0 ≤ S := inf_le_left
  have hP0D : P0.map C.subtype ≤ D := by
    rw [← hS0D]
    exact Subgroup.map_mono hP0S
  have hP0card : Nat.card (P0.map C.subtype) = 3 :=
    (Nat.card_congr (Subgroup.equivMapOfInjective P0 C.subtype Subtype.val_injective).toEquiv).symm.trans hP0c
  have hÑcard : Nat.card ((CFSG.pPrimeCore 3 ↥C).map C.subtype) = Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ C.subtype Subtype.val_injective).toEquiv).symm
  have hÑn : (((CFSG.pPrimeCore 3 ↥C).map C.subtype).subgroupOf M).Normal :=
    subgroupOf_normal_of_conj (fun m hm x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact conj_mem_pPrimeCore_map hCM hCn hm y hy)
  have hÑK : (CFSG.pPrimeCore 3 ↥C).map C.subtype ≤ CFSG.Open.GLBPrimeCore 3 M := by
    unfold CFSG.Open.GLBPrimeCore CFSG.Open.relPPrimeCore
    refine le_sSup ⟨?_, hÑn, ?_⟩
    · intro z hz
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hz
      exact hCM y.2
    · rw [hÑcard]
      exact CFSG.pPrimeCore_coprime_card
  have hK := sSup_normal_subgroupOf (H := M)
    (S := {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Nat.Coprime 3 (Nat.card N)})
    (fun N hN => ⟨hN.1, hN.2.1⟩)
  have hKM : CFSG.Open.GLBPrimeCore 3 M ≤ M := hK.1
  have hKn : ((CFSG.Open.GLBPrimeCore 3 M).subgroupOf M).Normal := hK.2
  have hKconj : ∀ m ∈ M, ∀ x ∈ CFSG.Open.GLBPrimeCore 3 M,
      m * x * m⁻¹ ∈ CFSG.Open.GLBPrimeCore 3 M := by
    intro m hm x hx
    exact Subgroup.mem_subgroupOf.mp
      (hKn.conj_mem ⟨x, hKM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m, hm⟩)
  have hcomapEq : P0 ⊔ CFSG.pPrimeCore 3 ↥C =
      (P0.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).comap
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) :=
    by rw [sup_comm]; exact (QuotientGroup.comap_map_mk' _ _).symm
  have hconjP : ∀ (m : G) (hm : m ∈ M) (y : ↥C), y ∈ P0 →
      conjEquiv hCM hCn hm y ∈ P0 ⊔ CFSG.pPrimeCore 3 ↥C := by
    intro m hm y hy
    rw [hcomapEq, Subgroup.mem_comap, hP0map, ← conjQuot_mk']
    have hyZ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) y ∈ Z := by
      rw [← hP0map]
      exact Subgroup.mem_map_of_mem _ hy
    have h2 := Subgroup.mem_map_of_mem (conjQuot hCM hCn hm).toMonoidHom hyZ
    rw [map_conjQuot_eq hCM hCn hm Z hZc hZle hunique] at h2
    exact h2
  have hRconj : ∀ m ∈ M, ∀ x ∈ P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M,
      m * x * m⁻¹ ∈ P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M := by
    intro m hm
    have hT : P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M ≤
        (P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M).comap (MulAut.conj m).toMonoidHom := by
      apply sup_le
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_comap.mpr ?_
        show m * (y : G) * m⁻¹ ∈ P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M
        rw [← conjEquiv_coe hCM hCn hm y]
        have h2 := Subgroup.mem_map_of_mem C.subtype (hconjP m hm y hy)
        rw [Subgroup.map_sup] at h2
        have hsub : P0.map C.subtype ⊔ (CFSG.pPrimeCore 3 ↥C).map C.subtype ≤
            P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M :=
          sup_le_sup le_rfl hÑK
        exact hsub h2
      · intro x hx
        refine Subgroup.mem_comap.mpr ?_
        exact (le_sup_right : CFSG.Open.GLBPrimeCore 3 M ≤
          P0.map C.subtype ⊔ CFSG.Open.GLBPrimeCore 3 M) (hKconj m hm x hx)
    intro x hx
    exact hT hx
  exact ⟨P0.map C.subtype, hP0D, hP0card, subgroupOf_normal_of_conj hRconj⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
