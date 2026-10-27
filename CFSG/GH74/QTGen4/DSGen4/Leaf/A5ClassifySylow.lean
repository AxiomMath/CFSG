module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyDict
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Certificates.A5GL42 (Mat4 Vec4 GroupFacts IsKlein klein normSet)
open scoped commutatorElement Matrix

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

variable {G : Type} [Group G] [Finite G] {P L E K : Subgroup G}

section SylowMap

variable {G' : Type*} [Group G']

theorem isSylowTwoOf_map {φ : G →* G'} {S L : Subgroup G} (h : IsSylowTwoOf S L) :
    IsSylowTwoOf (S.map φ) (L.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, ?_⟩
  have hsur := φ.subgroupMap_surjective L
  have hmap : (S.subgroupOf L).map (φ.subgroupMap L) = (S.map φ).subgroupOf (L.map φ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨s, hs, hsy⟩ := hy
      exact ⟨⟨s, h.1 hs⟩, hs, Subtype.ext hsy⟩
  have hdvd := Subgroup.index_map_dvd (H := S.subgroupOf L) hsur
  rw [hmap] at hdvd
  intro h2
  exact h.2.2 (h2.trans hdvd)

theorem isSylowTwoOf_map_iff {φ : G →* G'} (hφ : Function.Injective φ) {S L : Subgroup G} :
    IsSylowTwoOf (S.map φ) (L.map φ) ↔ IsSylowTwoOf S L := by
  refine ⟨fun h => ⟨(Subgroup.map_le_map_iff_of_injective hφ).1 h.1,
    h.2.1.of_equiv (Subgroup.equivMapOfInjective S φ hφ).symm, ?_⟩, isSylowTwoOf_map⟩
  have := h.2.2
  rwa [show ((S.map φ).subgroupOf (L.map φ)).index = (S.subgroupOf L).index from
    Subgroup.relIndex_map_map_of_injective S L hφ] at this

end SylowMap

structure SylowData {H : Finset Mat4} (M : A5Model P L E K H) (T : Subgroup G) where
  x : Mat4
  y : Mat4
  hx : x ∈ H
  hy : y ∈ H
  isKlein : IsKlein x y
  toA : ∀ t : ↥P, (t : G) ∈ T → glMat (M.F.M t) ∈ klein x y
  ofA : ∀ a ∈ klein x y, ∃ t : ↥P, (t : G) ∈ T ∧ glMat (M.F.M t) = a
  toB : ∀ n : ↥P, (n : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) →
    glMat (M.F.M n) ∈ normSet H (klein x y)
  ofB : ∀ b ∈ normSet H (klein x y),
    ∃ n : ↥P, (n : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) ∧ glMat (M.F.M n) = b

section Cards

variable {H : Finset Mat4}

theorem A5Model.mem_map_iff (M : A5Model P L E K H) (u : GL (Fin 4) (ZMod 2)) :
    u ∈ (L.subgroupOf P).map M.F.M ↔ glMat u ∈ H := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact M.imgL l (Subgroup.mem_subgroupOf.mp hl)
  · intro hu
    obtain ⟨l, hl, hlu⟩ := M.surjL _ hu
    exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, Units.ext hlu⟩

theorem A5Model.card_map (M : A5Model P L E K H) :
    Nat.card ((L.subgroupOf P).map M.F.M) = H.card := by
  classical
  let f : ↥((L.subgroupOf P).map M.F.M) → ↥H := fun u => ⟨glMat u.1, (M.mem_map_iff u.1).mp u.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u w huw
      exact Subtype.ext (Units.ext (congrArg Subtype.val huw))
    · rintro ⟨m, hm⟩
      obtain ⟨l, hl, hlm⟩ := M.surjL m hm
      exact ⟨⟨M.F.M l, (M.mem_map_iff _).mpr (by rw [hlm]; exact hm)⟩, Subtype.ext hlm⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem A5Model.sylow_card (hH : GroupFacts H) (h : A5Pre P L E K) (M : A5Model P L E K H)
    {T : Subgroup G} (hT : IsSylowTwoOf T L) :
    Nat.card ((T.subgroupOf P).map M.F.M) = 4 := by
  have hTL : T ≤ L := hT.1
  have hTp : IsSylowTwoOf (T.subgroupOf P) (L.subgroupOf P) := by
    rw [← isSylowTwoOf_map_iff (φ := P.subtype) P.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (hTL.trans h.le),
      Subgroup.map_subgroupOf_eq_of_le h.le]
    exact hT
  have hA := isSylowTwoOf_map (φ := M.F.M) hTp
  set A := (T.subgroupOf P).map M.F.M with hAdef
  set Hs := (L.subgroupOf P).map M.F.M with hHsdef
  have h60 : Nat.card Hs = 60 := by
    rw [M.card_map]; exact hH.2.2.2.1
  have hidx := Subgroup.index_mul_card (A.subgroupOf Hs)
  have hcardsub : Nat.card ↥(A.subgroupOf Hs) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [hcardsub, h60] at hidx
  obtain ⟨k, hk⟩ := hA.2.1.exists_card_eq
  rw [hk] at hidx
  have hodd := hA.2.2
  have hk3 : k < 3 := by
    by_contra hcon
    have h8 : (8 : ℕ) ∣ 2 ^ k := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have : (8 : ℕ) ∣ 60 := by
      rw [← hidx]
      exact Dvd.dvd.mul_left h8 _
    omega
  interval_cases k
  · exfalso; apply hodd; simp at hidx; omega
  · exfalso; apply hodd; simp at hidx; omega
  · simpa using hk

theorem A5Model.sylow_sq (hH : GroupFacts H) (h : A5Pre P L E K) (M : A5Model P L E K H)
    {T : Subgroup G} (hT : IsSylowTwoOf T L) {a : GL (Fin 4) (ZMod 2)}
    (ha : a ∈ (T.subgroupOf P).map M.F.M) : a * a = 1 := by
  have hcard := M.sylow_card hH h hT
  have hLmem : a ∈ (L.subgroupOf P).map M.F.M :=
    Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hT.1 (Subgroup.mem_subgroupOf.mp hx))) ha
  have hHmem : glMat a ∈ H := by
    obtain ⟨l, hl, rfl⟩ := hLmem
    exact M.imgL l (Subgroup.mem_subgroupOf.mp hl)
  have h4 : a ^ 4 = 1 := by
    have := pow_card_eq_one' (x := (⟨a, ha⟩ : ↥((T.subgroupOf P).map M.F.M)))
    rw [hcard] at this
    exact congrArg Subtype.val this
  have h44 : glMat a * glMat a * glMat a * glMat a = 1 := by
    have : a * a * a * a = 1 := by rw [← h4]; simp [pow_succ, mul_assoc]
    have := congrArg Units.val this
    simpa [glMat, Units.val_mul] using this
  obtain ⟨-, -, -, -, hno4, -⟩ := hH
  exact Units.ext (hno4 _ hHmem h44)

theorem exists_klein_elements_of_group {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 4)
    (hsq : ∀ a : X, a * a = 1) :
    ∃ u₁ u₂ : X, u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧ u₁ * u₂ = u₂ * u₁ ∧
      ∀ a : X, a = 1 ∨ a = u₁ ∨ a = u₂ ∨ a = u₁ * u₂ := by
  classical
  haveI : Fintype X := Fintype.ofFinite _
  have hinv : ∀ a : X, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_left (hsq a)
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : X, u₁ ≠ 1 := by
    by_contra hcon
    have h1 : ∀ x : X, x = 1 := fun x => by_contra fun h => hcon ⟨x, h⟩
    have : Nat.card X = 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
      exact ⟨1, h1⟩
    omega
  have hord : orderOf u₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq u₁) hu₁
  have hz : Nat.card (Subgroup.zpowers u₁) = 2 := by rw [Nat.card_zpowers, hord]
  have hztop : Subgroup.zpowers u₁ ≠ ⊤ := by
    intro ht
    rw [← Subgroup.card_eq_iff_eq_top] at ht
    omega
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : X, u₂ ∉ Subgroup.zpowers u₁ := by
    by_contra hcon
    exact hztop (eq_top_iff.mpr fun a _ => by_contra fun h => hcon ⟨a, h⟩)
  have hu₂1 : u₂ ≠ 1 := fun h => hu₂ (h ▸ Subgroup.one_mem _)
  have hu₁₂ : u₁ ≠ u₂ := fun h => hu₂ (h ▸ Subgroup.mem_zpowers u₁)
  have hcomm : u₁ * u₂ = u₂ * u₁ := by
    calc u₁ * u₂ = (u₁ * u₂)⁻¹ := (hinv _).symm
      _ = u₂ * u₁ := by rw [mul_inv_rev, hinv, hinv]
  have hd1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁₂
    have := eq_inv_of_mul_eq_one_right h
    rw [hinv] at this
    exact this.symm
  have hd2 : u₁ * u₂ ≠ u₁ := fun h => hu₂1 (by simpa using h)
  have hd3 : u₁ * u₂ ≠ u₂ := fun h => hu₁ (by simpa using h)
  have hS : (({1, u₁, u₂, u₁ * u₂} : Finset X)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hcard]
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hu₁, Ne.symm hu₂1, Ne.symm hd1]),
      Finset.card_insert_of_notMem (by simp [hu₁₂, Ne.symm hd2]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hd3]), Finset.card_singleton]
  refine ⟨u₁, u₂, hu₁, hu₂1, hu₁₂, hcomm, ?_⟩
  intro a
  have : a ∈ (({1, u₁, u₂, u₁ * u₂} : Finset X)) := by rw [hS]; exact Finset.mem_univ _
  simpa using this

end Cards

section Data

variable {H : Finset Mat4}

theorem matrix_eq_of_mulVec_eq {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ v : Vec4, A *ᵥ v = B *ᵥ v) : A = B := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v

theorem A5Model.exists_sylowData (hH : GroupFacts H) (h : A5Pre P L E K)
    (M : A5Model P L E K H) {T : Subgroup G} (hT : IsSylowTwoOf T L) :
    Nonempty (SylowData M T) := by
  classical
  set A := (T.subgroupOf P).map M.F.M with hAdef
  have hcard := M.sylow_card hH h hT
  have hsq : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (M.sylow_sq hH h hT a.2)
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂, hcomm, hall⟩ := exists_klein_elements_of_group hcard hsq
  have hlift : ∀ u ∈ A, ∃ t : ↥P, (t : G) ∈ T ∧ M.F.M t = u := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩
  have hAmem : ∀ t : ↥P, (t : G) ∈ T → M.F.M t ∈ A := fun t ht =>
    ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hHmem : ∀ u ∈ A, glMat u ∈ H := by
    intro u hu
    obtain ⟨t, htT, rfl⟩ := hlift u hu
    exact M.imgL t (hT.1 htT)
  set x : Mat4 := glMat (u₁ : GL (Fin 4) (ZMod 2)) with hxdef
  set y : Mat4 := glMat (u₂ : GL (Fin 4) (ZMod 2)) with hydef
  have hx1 : x ≠ 1 := fun e => hu₁ (Subtype.ext (Units.ext e))
  have hy1 : y ≠ 1 := fun e => hu₂ (Subtype.ext (Units.ext e))
  have hxy : x ≠ y := fun e => hu₁₂ (Subtype.ext (Units.ext e))
  have hxx : x * x = 1 := by
    have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) (hsq u₁)
    simpa [glMat, Units.val_mul] using this
  have hyy : y * y = 1 := by
    have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) (hsq u₂)
    simpa [glMat, Units.val_mul] using this
  have hxyc : x * y = y * x := by
    have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) hcomm
    simpa [glMat, Units.val_mul] using this
  have hkl : ∀ a ∈ klein x y, a = 1 ∨ a = x ∨ a = y ∨ a = x * y := by
    intro a ha
    simpa [klein] using ha
  have hklmem : ∀ a, (a = 1 ∨ a = x ∨ a = y ∨ a = x * y) → a ∈ klein x y := by
    intro a ha
    simpa [klein] using ha
  have toA : ∀ t : ↥P, (t : G) ∈ T → glMat (M.F.M t) ∈ klein x y := by
    intro t ht
    apply hklmem
    rcases hall ⟨M.F.M t, hAmem t ht⟩ with e | e | e | e
    · left; have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) e; simpa using this
    · right; left; have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) e; simpa using this
    · right; right; left
      have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) e; simpa using this
    · right; right; right
      have := congrArg (fun z : ↥A => glMat (z : GL (Fin 4) (ZMod 2))) e
      simpa [glMat, Units.val_mul] using this
  have ofA : ∀ a ∈ klein x y, ∃ t : ↥P, (t : G) ∈ T ∧ glMat (M.F.M t) = a := by
    intro a ha
    rcases hkl a ha with rfl | rfl | rfl | rfl
    · exact ⟨1, T.one_mem, by simp [glMat]⟩
    · obtain ⟨t, ht, e⟩ := hlift u₁ u₁.2
      exact ⟨t, ht, by rw [e]⟩
    · obtain ⟨t, ht, e⟩ := hlift u₂ u₂.2
      exact ⟨t, ht, by rw [e]⟩
    · obtain ⟨t, ht, e⟩ := hlift ((u₁ : GL (Fin 4) (ZMod 2)) * u₂) (A.mul_mem u₁.2 u₂.2)
      exact ⟨t, ht, by rw [e, hxdef, hydef]; simp [glMat, Units.val_mul]⟩
  have toB : ∀ n : ↥P, (n : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) →
      glMat (M.F.M n) ∈ normSet H (klein x y) := by
    intro n hn
    unfold normSet
    rw [Finset.mem_filter]
    refine ⟨M.imgL n hn.1, fun a ha => ?_⟩
    obtain ⟨t, htT, rfl⟩ := ofA a ha
    have htn : ((n * t * n⁻¹ : ↥P) : G) ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hn.2 (t : G)).mp htT
      simpa using this
    refine ⟨glMat (M.F.M (n * t * n⁻¹)), toA _ htn, fun v => ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [map_mul, map_mul, map_inv]
    simp only [glMat, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have ofB : ∀ b ∈ normSet H (klein x y),
      ∃ n : ↥P, (n : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) ∧ glMat (M.F.M n) = b := by
    intro b hb
    unfold normSet at hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbH, hbN⟩ := hb
    obtain ⟨n, hnL, hnb⟩ := M.surjL b hbH
    refine ⟨n, ⟨hnL, ?_⟩, hnb⟩
    have hconj : ∀ t ∈ T, (n : G) * t * (n : G)⁻¹ ∈ T := by
      intro t htT
      have htP : t ∈ P := h.le (hT.1 htT)
      obtain ⟨a', ha', hva⟩ := hbN (glMat (M.F.M ⟨t, htP⟩)) (toA ⟨t, htP⟩ htT)
      obtain ⟨t', ht'T, ht'a⟩ := ofA a' ha'
      have hmat : glMat (M.F.M n) * glMat (M.F.M ⟨t, htP⟩) = a' * glMat (M.F.M n) := by
        exact matrix_eq_of_mulVec_eq fun v => by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hnb]
          exact hva v
      rw [← ht'a] at hmat
      have hmatGL : M.F.M n * M.F.M ⟨t, htP⟩ = M.F.M t' * M.F.M n :=
        Units.ext hmat
      have hc : M.F.M (n * ⟨t, htP⟩ * n⁻¹ * t'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hmatGL]
        group
      have hcL : ((n * ⟨t, htP⟩ * n⁻¹ * t'⁻¹ : ↥P) : G) ∈ L := by
        have h1 : (n : G) ∈ L := hnL
        have h2 : t ∈ L := hT.1 htT
        have h3 : (t' : G) ∈ L := hT.1 ht'T
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact L.mul_mem (L.mul_mem (L.mul_mem h1 h2) (L.inv_mem h1)) (L.inv_mem h3)
      have hcT : ((n * ⟨t, htP⟩ * n⁻¹ * t'⁻¹ : ↥P) : G) ∈ T :=
        hT.pCoreOf_le ((M.kerL _ hcL).mp hc)
      have : (n : G) * t * (n : G)⁻¹ = ((n * ⟨t, htP⟩ * n⁻¹ * t'⁻¹ : ↥P) : G) * (t' : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [this]
      exact T.mul_mem hcT ht'T
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨t, ht, rfl⟩
      exact hconj t ht
    · rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective]
  exact ⟨⟨x, y, hHmem _ u₁.2, hHmem _ u₂.2, ⟨hx1, hy1, hxy, hxx, hyy, hxyc⟩, toA, ofA, toB,
    ofB⟩⟩

theorem SylowData.mem_kleinGroups {H : Finset Mat4} {M : A5Model P L E K H} {T : Subgroup G}
    (sd : SylowData M T) : klein sd.x sd.y ∈ Certificates.A5GL42.kleinGroups H := by
  unfold Certificates.A5GL42.kleinGroups
  rw [Finset.mem_image]
  refine ⟨(sd.x, sd.y), ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr ⟨sd.hx, sd.hy⟩, sd.isKlein⟩

theorem img_mem_invSubspaces_of {H : Finset Mat4} (hF : Certificates.A5GL42.Facts)
    (h : A5Pre P L E K) (M : A5Model P L E K H) {B : Finset Mat4} {X : Subgroup G}
    (hB : ∀ b ∈ B, ∃ n : ↥P, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧
      glMat (M.F.M n) = b) :
    img M.F X ∈ Certificates.A5GL42.invSubspaces B := by
  unfold Certificates.A5GL42.invSubspaces
  rw [Finset.mem_filter]
  refine ⟨hF.subspaces_complete _ (zero_mem_img _ _)
    (fun u hu w hw => add_mem_img _ _ hu hw), ?_⟩
  intro b hb w hw
  obtain ⟨n, hn, hnb⟩ := hB b hb
  obtain ⟨e, heX, rfl⟩ := mem_img.mp hw
  have hact := M.F.act n e (conjE h.norm_E n e) (coe_conjE _ _ _)
  rw [← hnb, hact]
  refine mem_img.mpr ⟨conjE h.norm_E n e, ?_, rfl⟩
  rw [coe_conjE]
  exact (Subgroup.mem_normalizer_iff.mp hn _).mp heX

theorem img_mem_invSubspaces {H : Finset Mat4} (hF : Certificates.A5GL42.Facts)
    (h : A5Pre P L E K) (M : A5Model P L E K H) {T : Subgroup G} (sd : SylowData M T)
    {X : Subgroup G}
    (hXN : L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    img M.F X ∈ Certificates.A5GL42.invSubspaces (normSet H (klein sd.x sd.y)) :=
  img_mem_invSubspaces_of hF h M fun b hb => by
    obtain ⟨n, hn, hnb⟩ := sd.ofB b hb
    exact ⟨n, hXN hn, hnb⟩

theorem A5Model.eq_or_eq_of_normalizes {H : Finset Mat4} (hF : Certificates.A5GL42.Facts)
    (hH : GroupFacts H) (h : A5Pre P L E K) (M : A5Model P L E K H) {X : Subgroup G}
    (hKX : K ≤ X) (hXE : X ≤ E) (hLX : L ≤ Subgroup.normalizer (X : Set G)) :
    X = K ∨ X = E := by
  have hW : img M.F X ∈ Certificates.A5GL42.invSubspaces H :=
    img_mem_invSubspaces_of hF h M fun b hb => by
      obtain ⟨l, hl, hlb⟩ := M.surjL b hb
      exact ⟨l, hLX hl, hlb⟩
  obtain ⟨-, -, -, -, -, hirr⟩ := hH
  rw [hirr] at hW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with hW | hW
  · left
    exact ext_of_img M.F hKX hXE le_rfl h.sec.1 (by rw [hW, img_bot_of_ker])
  · right
    exact ext_of_img M.F hKX hXE h.sec.1 le_rfl (by rw [hW, img_top])

theorem A5Model.exists_act_eq_of_mem_sup (M : A5Model P L E K H) (h : A5Pre P L E K)
    {T : Subgroup G} (hT : IsSylowTwoOf T L) {s : G} (hs : s ∈ T ⊔ pCoreOf 2 P) :
    ∃ hsP : s ∈ P, ∃ t : ↥P, (t : G) ∈ T ∧ M.F.M ⟨s, hsP⟩ = M.F.M t ∧ s * (t : G)⁻¹ ∈ pCoreOf 2 P := by
  have hTP : T ≤ P := hT.1.trans h.le
  have hQnorm : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf P)
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  obtain ⟨t, htT, hst⟩ := exists_mul_inv_mem_of_mem_sup hTP hQnorm s hs
  have hsP : s ∈ P := (sup_le hTP hQP) hs
  refine ⟨hsP, ⟨t, hTP htT⟩, htT, ?_, hst⟩
  have h1 := M.core ⟨s * t⁻¹, P.mul_mem hsP (P.inv_mem (hTP htT))⟩ hst
  have h2 : (⟨s, hsP⟩ : ↥P) = ⟨s * t⁻¹, P.mul_mem hsP (P.inv_mem (hTP htT))⟩ * ⟨t, hTP htT⟩ :=
    Subtype.ext (by simp)
  rw [h2, map_mul, h1, one_mul]

theorem A5Model.mem_core_of_act_eq_one (M : A5Model P L E K H) (h : A5Pre P L E K)
    {T : Subgroup G} (hT : IsSylowTwoOf T L) {s : G} (hs : s ∈ T ⊔ pCoreOf 2 P) (hsP : s ∈ P)
    (h1 : M.F.M ⟨s, hsP⟩ = 1) : s ∈ pCoreOf 2 P := by
  obtain ⟨hsP', t, htT, hMst, hst⟩ := M.exists_act_eq_of_mem_sup h hT hs
  have hM1 : M.F.M t = 1 := by rw [← hMst]; exact h1
  have htQ : (t : G) ∈ pCoreOf 2 P :=
    pCoreOf_le_pCoreOf h.le h.norm_L ((M.kerL t (hT.1 htT)).mp hM1)
  have : s = (s * (t : G)⁻¹) * (t : G) := by simp
  rw [this]
  exact (pCoreOf 2 P).mul_mem hst htQ

theorem klein_card {x y : Mat4} (hk : IsKlein x y) : (klein x y).card = 4 := by
  obtain ⟨hx1, hy1, hxy, hxx, hyy, -⟩ := hk
  have d1 : x * y ≠ 1 := fun h => hxy (by
    calc x = x * 1 := (mul_one x).symm
      _ = x * (x * y) := by rw [h]
      _ = (x * x) * y := (mul_assoc x x y).symm
      _ = y := by rw [hxx, one_mul])
  have d2 : x * y ≠ x := fun h => hy1 (by
    calc y = (x * x) * y := by rw [hxx, one_mul]
      _ = x * (x * y) := mul_assoc x x y
      _ = x * x := by rw [h]
      _ = 1 := hxx)
  have d3 : x * y ≠ y := fun h => hx1 (by
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := (mul_assoc x y y).symm
      _ = y * y := by rw [h]
      _ = 1 := hyy)
  unfold klein
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1, Ne.symm d1]),
    Finset.card_insert_of_notMem (by simp [hxy, Ne.symm d2]),
    Finset.card_insert_of_notMem (by simp [Ne.symm d3]), Finset.card_singleton]

end Data

end CFSG.GH74.QTGen4.DSGen4
