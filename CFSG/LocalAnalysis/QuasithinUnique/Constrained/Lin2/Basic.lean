module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem conjR_def (X : Subgroup G) (g : G) : conjR X g = X.map (MulAut.conj g⁻¹).toMonoidHom := rfl

theorem conjR_eq_conjSubgroup (X : Subgroup G) (g : G) : conjR X g = conjSubgroup X g := rfl

theorem mem_conjR {X : Subgroup G} {g y : G} : y ∈ conjR X g ↔ g * y * g⁻¹ ∈ X :=
  mem_conjSubgroup_iff

theorem mem_conjR_iff' {X : Subgroup G} {g y : G} : y ∈ conjR X g ↔ ∃ x ∈ X, y = g⁻¹ * x * g := by
  rw [mem_conjR]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨x, hx, rfl⟩
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hx

theorem conjR_conjR (X : Subgroup G) (g h : G) : conjR (conjR X g) h = conjR X (g * h) :=
  conjSubgroup_conjSubgroup X g h

@[simp] theorem conjR_one (X : Subgroup G) : conjR X 1 = X := conjSubgroup_one X

theorem conjR_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) : conjR X g ≤ conjR Y g := by
  intro y hy
  rw [mem_conjR] at hy ⊢
  exact h hy

theorem conjR_le_iff {X Y : Subgroup G} {g : G} : conjR X g ≤ Y ↔ X ≤ conjR Y g⁻¹ := by
  constructor
  · intro h x hx
    rw [mem_conjR]
    apply h
    rw [mem_conjR]
    have : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rw [this]
    exact hx
  · intro h y hy
    rw [mem_conjR] at hy
    have := h hy
    rw [mem_conjR] at this
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this

theorem conjR_inf (X Y : Subgroup G) (g : G) : conjR (X ⊓ Y) g = conjR X g ⊓ conjR Y g := by
  ext y
  simp [mem_conjR]

theorem conjR_sup (X Y : Subgroup G) (g : G) : conjR (X ⊔ Y) g = conjR X g ⊔ conjR Y g :=
  Subgroup.map_sup X Y _

@[simp] theorem conjR_bot (g : G) : conjR (⊥ : Subgroup G) g = ⊥ := by
  ext y
  simp [mem_conjR]

@[simp] theorem conjR_top (g : G) : conjR (⊤ : Subgroup G) g = ⊤ := by
  ext y
  simp [mem_conjR]

theorem conjR_eq_self_iff {X : Subgroup G} {g : G} :
    conjR X g = X ↔ g ∈ Subgroup.normalizer (X : Set G) := conjSubgroup_eq_iff_mem_normalizer

theorem conjR_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : conjR X g = X :=
  conjR_eq_self_iff.mpr hg

theorem conjR_eq_of_mem {X : Subgroup G} {g : G} (hg : g ∈ X) : conjR X g = X :=
  conjR_eq_of_mem_normalizer (Subgroup.le_normalizer hg)

theorem card_conjR (X : Subgroup G) (g : G) : Nat.card (conjR X g) = Nat.card X :=
  card_map_equiv (MulAut.conj g⁻¹) X

theorem isPGroup_conjR_iff (p : ℕ) {X : Subgroup G} {g : G} :
    IsPGroup p (conjR X g) ↔ IsPGroup p X :=
  isPGroup_map_equiv_iff p (MulAut.conj g⁻¹) X

theorem conjR_eq_bot_iff {X : Subgroup G} {g : G} : conjR X g = ⊥ ↔ X = ⊥ :=
  map_equiv_eq_bot_iff (MulAut.conj g⁻¹) X

theorem conjR_normalizer (X : Subgroup G) (g : G) :
    Subgroup.normalizer ((conjR X g : Subgroup G) : Set G) =
      conjR (Subgroup.normalizer (X : Set G)) g :=
  normalizer_map_equiv (MulAut.conj g⁻¹) X

theorem conjR_centralizer (X : Subgroup G) (g : G) :
    Subgroup.centralizer ((conjR X g : Subgroup G) : Set G) =
      conjR (Subgroup.centralizer (X : Set G)) g :=
  centralizer_map_equiv (MulAut.conj g⁻¹) X

theorem conjR_pCoreOf (p : ℕ) (X : Subgroup G) (g : G) :
    pCoreOf p (conjR X g) = conjR (pCoreOf p X) g :=
  pCoreOf_map_equiv p (MulAut.conj g⁻¹) X

theorem conjR_conjR_inv (X : Subgroup G) (g : G) : conjR (conjR X g) g⁻¹ = X := by
  rw [conjR_conjR]; simp

theorem conjR_inv_conjR (X : Subgroup G) (g : G) : conjR (conjR X g⁻¹) g = X := by
  rw [conjR_conjR]; simp

theorem conjR_mul (X : Subgroup G) (g h : G) : conjR X (g * h) = conjR (conjR X g) h :=
  (conjR_conjR X g h).symm

theorem card_conjR_eq_iff {X Y : Subgroup G} {g : G} (h : X ≤ Y) :
    conjR X g ≤ conjR Y g := conjR_mono h g

theorem le_normalizer_iff_conjR {X Y : Subgroup G} :
    X ≤ Subgroup.normalizer (Y : Set G) ↔ ∀ x ∈ X, conjR Y x = Y :=
  forall_congr' fun _ => forall_congr' fun _ => conjR_eq_self_iff.symm

end Conj

theorem openPCore_eq_pCore (p : ℕ) (X : Type*) [Group X] :
    CFSG.Open.pCore p X = CFSG.pCore p X :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup (G := X) p

section Orders

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {L W : Subgroup G} (h : ∀ g ∈ L, ∀ y ∈ W, g * y * g⁻¹ ∈ W) :
    L ≤ Subgroup.normalizer (W : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (L.inv_mem hg) _ hy
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at this

theorem eq_of_le_of_card_le' [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hc : Nat.card B ≤ Nat.card A) : A = B :=
  (Subgroup.eq_of_le_of_card_ge hAB hc)


theorem relIndex_sup_of_le_normalizer {B A : Subgroup G} (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hA).toEquiv.symm

theorem card_sup_mul_card_inf {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h1 := relIndex_sup_of_le_normalizer hA
  have hK : Nat.card (A ⊔ B : Subgroup G) = Nat.card B * B.relIndex (A ⊔ B) := by
    have := Subgroup.card_mul_index (B.subgroupOf (A ⊔ B))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv] at this
    exact this.symm
  have hA' : Nat.card A = Nat.card (A ⊓ B : Subgroup G) * B.relIndex A := by
    have := Subgroup.card_mul_index ((A ⊓ B).subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv] at this
    have e : ((A ⊓ B).subgroupOf A).index = B.relIndex A := by
      have := Subgroup.inf_relIndex_right B A
      rw [inf_comm] at this
      exact this
    rw [e] at this
    exact this.symm
  rw [hK, h1]
  conv_rhs => rw [hA']
  ring

end Orders

section Cyclic

variable {G : Type*} [Group G]

theorem eq_of_sq_eq_one_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {x y : Q}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have : Fintype Q := Fintype.ofFinite Q
  have hcard := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset Q) ⊆ Finset.univ.filter (fun a : Q => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, x, y} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxy
    · simp [Ne.symm hx1, Ne.symm hy1]
  have := Finset.card_le_card hsub
  omega

theorem sup_zpowers_subgroupOf_eq_top {T N : Subgroup G} (hNT : N ≤ T) {t₀ : G}
    (hT : T = N ⊔ Subgroup.zpowers t₀) :
    N.subgroupOf T ⊔ (Subgroup.zpowers t₀).subgroupOf T = ⊤ := by
  have ht₀ : t₀ ∈ T := hT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  rw [← Subgroup.subgroupOf_sup hNT (Subgroup.zpowers_le.mpr ht₀), ← hT]
  exact Subgroup.subgroupOf_self T

theorem commutator_le_of_sup_zpowers {T N : Subgroup G} (hNT : N ≤ T)
    (hN : T ≤ Subgroup.normalizer (N : Set G)) {t₀ : G} (hT : T = N ⊔ Subgroup.zpowers t₀) :
    ⁅T, T⁆ ≤ N := by
  have hnorm : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hsup := sup_zpowers_subgroupOf_eq_top hNT hT
  have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (⁅(⟨x, hx⟩ : T), (⟨y, hy⟩ : T)⁆ : T) ∈ commutator T := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 := hc h1
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : ((⁅(⟨x, hx⟩ : T), (⟨y, hy⟩ : T)⁆ : T) : G) = ⁅x, y⁆ := by
    simp [commutatorElement_def]
  rw [h3] at h2
  exact h2

theorem inv_mul_mem_of_sq_eq_one [Finite G] {T N : Subgroup G} (hNT : N ≤ T)
    (hN : T ≤ Subgroup.normalizer (N : Set G)) {t₀ : G} (hT : T = N ⊔ Subgroup.zpowers t₀)
    {a b : G} (ha : a ∈ T) (hb : b ∈ T) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (haN : a ∉ N)
    (hbN : b ∉ N) : a⁻¹ * b ∈ N := by
  have hnorm : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have ht₀ : t₀ ∈ T := hT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have hsup := sup_zpowers_subgroupOf_eq_top hNT hT
  have : IsCyclic (T ⧸ N.subgroupOf T) := by
    refine ⟨⟨QuotientGroup.mk (⟨t₀, ht₀⟩ : T), fun q => ?_⟩⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    have hc : c ∈ N.subgroupOf T ⊔ (Subgroup.zpowers t₀).subgroupOf T := hsup ▸ Subgroup.mem_top c
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hc
    have hz' : (z : G) ∈ Subgroup.zpowers t₀ := hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'
    have hzk : z = (⟨t₀, ht₀⟩ : T) ^ k := Subtype.ext (by simpa using hk.symm)
    refine ⟨k, ?_⟩
    rw [← hyz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul, hzk]
    simp
  let π : T →* T ⧸ N.subgroupOf T := QuotientGroup.mk' _
  have hπ : ∀ w : T, (w : G) ∈ N ↔ π w = 1 := by
    intro w
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπa : π ⟨a, ha⟩ ^ 2 = 1 := by
    rw [← map_pow]; exact (congrArg π (Subtype.ext (by simpa using ha2))).trans (map_one π)
  have hπb : π ⟨b, hb⟩ ^ 2 = 1 := by
    rw [← map_pow]; exact (congrArg π (Subtype.ext (by simpa using hb2))).trans (map_one π)
  have hπa1 : π ⟨a, ha⟩ ≠ 1 := fun h => haN ((hπ ⟨a, ha⟩).2 h)
  have hπb1 : π ⟨b, hb⟩ ≠ 1 := fun h => hbN ((hπ ⟨b, hb⟩).2 h)
  have heq := eq_of_sq_eq_one_of_isCyclic hπa hπb hπa1 hπb1
  have : π (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by rw [map_mul, map_inv, heq, inv_mul_cancel]
  have := (hπ _).2 this
  simpa using this

theorem eq_sup_zpowers_of_relIndex_two {S T : Subgroup G} (hST : S ≤ T) (h2 : S.relIndex T = 2)
    {t : G} (htT : t ∈ T) (htS : t ∉ S) : T = S ⊔ Subgroup.zpowers t := by
  have hK : S ⊔ Subgroup.zpowers t ≤ T := sup_le hST (Subgroup.zpowers_le.mpr htT)
  have hmul := Subgroup.relIndex_mul_relIndex S (S ⊔ Subgroup.zpowers t) T le_sup_left hK
  rw [h2] at hmul
  have h1 : S.relIndex (S ⊔ Subgroup.zpowers t) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact htS (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  have hdvd : S.relIndex (S ⊔ Subgroup.zpowers t) ∣ 2 := ⟨_, hmul.symm⟩
  have h2' : S.relIndex (S ⊔ Subgroup.zpowers t) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h h1
    · exact h
  rw [h2'] at hmul
  have : (S ⊔ Subgroup.zpowers t).relIndex T = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 this) hK

theorem inv_mul_mem_of_relIndex_two {S T : Subgroup G} (h2 : S.relIndex T = 2) {a b : G}
    (ha : a ∈ T) (hb : b ∈ T) (haS : a ∉ S) (hbS : b ∉ S) : a⁻¹ * b ∈ S := by
  have h2' : (S.subgroupOf T).index = 2 := h2
  have := (Subgroup.mul_mem_iff_of_index_two h2' (a := (⟨a, ha⟩ : T)⁻¹) (b := ⟨b, hb⟩))
  have h1 : ((⟨a, ha⟩ : T)⁻¹ * ⟨b, hb⟩ ∈ S.subgroupOf T) := by
    rw [this]
    simp only [inv_mem_iff]
    exact iff_of_false (fun h => haS h) (fun h => hbS h)
  have h3 := Subgroup.mem_subgroupOf.1 h1
  simpa using h3

theorem le_normalizer_of_relIndex_two {S T : Subgroup G} (hST : S ≤ T) (h2 : S.relIndex T = 2) :
    T ≤ Subgroup.normalizer (S : Set G) := by
  have : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hST).1 this

theorem sq_mem_of_relIndex_two {S T : Subgroup G} (h2 : S.relIndex T = 2)
    {t : G} (htT : t ∈ T) : t ^ 2 ∈ S := by
  have hnorm : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  have h2' : (S.subgroupOf T).index = 2 := h2
  have := Subgroup.pow_index_mem (S.subgroupOf T) (⟨t, htT⟩ : T)
  rw [h2', Subgroup.mem_subgroupOf] at this
  simpa using this

theorem exists_involution_of_isPGroup [Finite G] {F : Subgroup G} (hF : IsPGroup 2 F)
    (hbot : F ≠ ⊥) : ∃ f ∈ F, f ^ 2 = 1 ∧ f ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hF
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hbot
    rw [← Subgroup.card_eq_one]
    simpa using hk
  have hdvd : 2 ∣ Nat.card F := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 hdvd
  refine ⟨x, x.2, ?_, ?_⟩
  · have : (x : G) ^ 2 = ((x ^ 2 : F) : G) := by simp
    rw [this, ← hx, pow_orderOf_eq_one]; rfl
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem thompsonJ_le_self (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup₂_le fun _ hA => hA.1

end Cyclic

section Transfer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_top_of_simple_nonabelian [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hmem : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

theorem transfer_contradiction_cyclic [IsSimpleGroup G] (hnc : ∃ a b : G, a * b ≠ b * a)
    {T N : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T)
    (hN : T ≤ Subgroup.normalizer (N : Set G)) {t₀ : G} (hcyc : T = N ⊔ Subgroup.zpowers t₀)
    {t : G} (htT : t ∈ T) (htN : t ∉ N) (ht2 : t ^ 2 = 1)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ N) : False := by
  have hindex : Nat.Coprime 2 T.index := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    have := hT.2.2
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e] at this
  have hnorm : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hcomm := commutator_le_of_sup_zpowers hNT hN hcyc
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 (fun h => htN (h ▸ N.one_mem))
  have key := generalized_thompson_transfer_two hindex ⟨hNT, hnorm⟩ hcomm htT htN hord (by
    intro a ha
    have ha2 : (a⁻¹ * t * a) ^ 2 = 1 := by
      have : (a⁻¹ * t * a) ^ 2 = a⁻¹ * t ^ 2 * a := by simp only [pow_two]; group
      rw [this, ht2]; simp
    have := inv_mul_mem_of_sq_eq_one hNT hN hcyc htT ha ht2 ha2 htN (hfus a)
    simpa using this)
  exact key (commutator_eq_top_of_simple_nonabelian hnc ▸ Subgroup.mem_top t)

end Transfer

section Cfg

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.simple (h : Lin2Cfg G T M H S L n D) : IsSimpleGroup G :=
  h.cs.setting.simple

theorem Lin2Cfg.nonabelian (h : Lin2Cfg G T M H S L n D) : ∃ a b : G, a * b ≠ b * a :=
  h.cs.setting.nonabelian

theorem Lin2Cfg.sylowT (h : Lin2Cfg G T M H S L n D) : IsSylowTwoOf T ⊤ :=
  h.cs.setting.sylow

theorem Lin2Cfg.S_le_T (h : Lin2Cfg G T M H S L n D) : S ≤ T := h.cs.le_T

theorem Lin2Cfg.T_le_M (h : Lin2Cfg G T M H S L n D) : T ≤ M := h.cs.setting.le

theorem Lin2Cfg.S_ne_T (h : Lin2Cfg G T M H S L n D) : S ≠ T := h.cs.ne_T

theorem Lin2Cfg.S_le_H (h : Lin2Cfg G T M H S L n D) : S ≤ H := h.cs.sylow.1

end Cfg

end CFSG.QuasithinUnique.Lin2
