
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.A5.Kc3Cover

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] (K : Subgroup G)

@[expose] def zK : Subgroup G := (Subgroup.center ↥K).map K.subtype

@[expose] def nK : Subgroup G := Subgroup.normalizer (K : Set G)

theorem zK_le : zK K ≤ K := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem K_le_nK : K ≤ nK K := Subgroup.le_normalizer

theorem mem_zK {z : G} : z ∈ zK K ↔ ∃ h : z ∈ K, (⟨z, h⟩ : ↥K) ∈ Subgroup.center ↥K := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨z, h⟩, hc, rfl⟩

theorem zK_conj {n : G} (hn : n ∈ nK K) {z : G} (hz : z ∈ zK K) : n * z * n⁻¹ ∈ zK K := by
  obtain ⟨hzK, hzc⟩ := (mem_zK K).1 hz
  have hnK : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hn z).1 hzK
  rw [mem_zK]
  refine ⟨hnK, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro k
  have hk' : n⁻¹ * (k : G) * n ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 ((nK K).inv_mem hn) (k : G)).1 k.2
    simpa using this
  have hc := Subgroup.mem_center_iff.1 hzc ⟨n⁻¹ * k * n, hk'⟩
  have hc' : (n⁻¹ * (k : G) * n) * z = z * (n⁻¹ * (k : G) * n) := congrArg Subtype.val hc
  apply Subtype.ext
  show (k : G) * (n * z * n⁻¹) = n * z * n⁻¹ * k
  calc (k : G) * (n * z * n⁻¹) = n * ((n⁻¹ * k * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * k * n)) * n⁻¹ := by rw [hc']
    _ = n * z * n⁻¹ * k := by group

instance zn_normal : ((zK K).subgroupOf (nK K)).Normal :=
  ⟨fun z hz n => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    simpa using zK_conj K n.2 hz⟩

abbrev Gbar : Type := ↥(nK K) ⧸ (zK K).subgroupOf (nK K)

@[expose] def psi : ↥(nK K) →* Gbar K := QuotientGroup.mk' ((zK K).subgroupOf (nK K))

theorem psi_surjective : Function.Surjective (psi K) := QuotientGroup.mk_surjective

theorem psi_eq_one {n : ↥(nK K)} : psi K n = 1 ↔ (n : G) ∈ zK K := by
  rw [psi, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem psi_eq_iff {n m : ↥(nK K)} : psi K n = psi K m ↔ (n : G)⁻¹ * (m : G) ∈ zK K := by
  rw [psi, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  rfl

@[expose] def img (A : Subgroup G) : Subgroup (Gbar K) := (A.subgroupOf (nK K)).map (psi K)

@[expose] def pre (B : Subgroup (Gbar K)) : Subgroup G := (B.comap (psi K)).map (nK K).subtype

theorem mem_img {A : Subgroup G} {y : Gbar K} :
    y ∈ img K A ↔ ∃ (a : G) (h : a ∈ nK K), a ∈ A ∧ psi K ⟨a, h⟩ = y := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, a.2, Subgroup.mem_subgroupOf.1 ha, rfl⟩
  · rintro ⟨a, h, ha, rfl⟩
    exact ⟨⟨a, h⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩

theorem mem_pre {B : Subgroup (Gbar K)} {g : G} :
    g ∈ pre K B ↔ ∃ h : g ∈ nK K, psi K ⟨g, h⟩ ∈ B := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem img_mono {A B : Subgroup G} (h : A ≤ B) : img K A ≤ img K B :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem pre_mono {A B : Subgroup (Gbar K)} (h : A ≤ B) : pre K A ≤ pre K B := by
  intro g hg
  obtain ⟨hn, hA⟩ := (mem_pre K).1 hg
  exact (mem_pre K).2 ⟨hn, h hA⟩

theorem pre_le_nK (B : Subgroup (Gbar K)) : pre K B ≤ nK K := fun _ hg => ((mem_pre K).1 hg).1

theorem img_pre (B : Subgroup (Gbar K)) : img K (pre K B) = B := by
  ext y
  rw [mem_img]
  constructor
  · rintro ⟨a, h, ha, rfl⟩
    exact ((mem_pre K).1 ha).2
  · intro hy
    obtain ⟨n, rfl⟩ := psi_surjective K y
    exact ⟨n, n.2, (mem_pre K).2 ⟨n.2, hy⟩, rfl⟩

theorem pre_img_of_zK_le {A : Subgroup G} (hAN : A ≤ nK K) (hZA : zK K ≤ A) :
    pre K (img K A) = A := by
  ext g
  constructor
  · intro hg
    obtain ⟨hn, hy⟩ := (mem_pre K).1 hg
    obtain ⟨a, ha, haA, hag⟩ := (mem_img K).1 hy
    have h1 := (psi_eq_iff K).1 hag
    have h2 : g = a * (a⁻¹ * g) := by group
    rw [h2]
    exact A.mul_mem haA (hZA h1)
  · intro hg
    exact (mem_pre K).2 ⟨hAN hg, (mem_img K).2 ⟨g, hAN hg, hg, rfl⟩⟩

theorem le_pre_img {A : Subgroup G} (hAN : A ≤ nK K) : A ≤ pre K (img K A) := fun g hg =>
  (mem_pre K).2 ⟨hAN hg, (mem_img K).2 ⟨g, hAN hg, hg, rfl⟩⟩

theorem zK_le_pre (B : Subgroup (Gbar K)) : zK K ≤ pre K B := by
  intro z hz
  have hzN : z ∈ nK K := K_le_nK K (zK_le K hz)
  refine (mem_pre K).2 ⟨hzN, ?_⟩
  have : psi K ⟨z, hzN⟩ = 1 := (psi_eq_one K).2 hz
  rw [this]
  exact B.one_mem

theorem img_sup {A B : Subgroup G} (hA : A ≤ nK K) (hB : B ≤ nK K) :
    img K (A ⊔ B) = img K A ⊔ img K B := by
  rw [img, img, img, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem img_conj_mem {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) {a : G}
    (ha : a ∈ nK K) (haA : a ∈ A) {z : Gbar K} (hz : z ∈ img K B) :
    psi K ⟨a, ha⟩ * z * (psi K ⟨a, ha⟩)⁻¹ ∈ img K B := by
  obtain ⟨b, hb, hbB, rfl⟩ := (mem_img K).1 hz
  refine (mem_img K).2 ⟨a * b * a⁻¹, (nK K).mul_mem ((nK K).mul_mem ha hb) ((nK K).inv_mem ha),
    (Subgroup.mem_normalizer_iff.1 (h haA) b).1 hbB, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem img_le_normalizer {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    img K A ≤ Subgroup.normalizer (img K B : Set (Gbar K)) := by
  intro y hy
  obtain ⟨a, ha, haA, rfl⟩ := (mem_img K).1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => img_conj_mem K h ha haA hz, fun hz => ?_⟩
  have h1 := img_conj_mem K h ((nK K).inv_mem ha) (A.inv_mem haA) hz
  have h2 : psi K ⟨a⁻¹, (nK K).inv_mem ha⟩ = (psi K ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h2, inv_inv] at h1
  simpa [mul_assoc] using h1

theorem img_isPGroup {A : Subgroup G} (hA : IsPGroup 2 A) : IsPGroup 2 (img K A) := by
  intro y
  obtain ⟨a, ha, haA, hay⟩ := (mem_img K).1 y.2
  obtain ⟨k, hk⟩ := hA ⟨a, haA⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have : (y : Gbar K) = psi K ⟨a, ha⟩ := hay.symm
  show (y : Gbar K) ^ 2 ^ k = 1
  rw [this, ← map_pow]
  have : (⟨a, ha⟩ : ↥(nK K)) ^ 2 ^ k = 1 := Subtype.ext hk'
  rw [this, map_one]

theorem pre_conj_mem {A B : Subgroup (Gbar K)} (h : A ≤ Subgroup.normalizer (B : Set (Gbar K)))
    {x : G} (hx : x ∈ pre K A) {g : G} (hg : g ∈ pre K B) : x * g * x⁻¹ ∈ pre K B := by
  obtain ⟨hxN, hxA⟩ := (mem_pre K).1 hx
  obtain ⟨hgN, hgB⟩ := (mem_pre K).1 hg
  refine (mem_pre K).2 ⟨(nK K).mul_mem ((nK K).mul_mem hxN hgN) ((nK K).inv_mem hxN), ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 (h hxA) (psi K ⟨g, hgN⟩)).1 hgB
  have h2 : psi K ⟨x * g * x⁻¹, (nK K).mul_mem ((nK K).mul_mem hxN hgN) ((nK K).inv_mem hxN)⟩ =
      psi K ⟨x, hxN⟩ * psi K ⟨g, hgN⟩ * (psi K ⟨x, hxN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h2]
  exact h1

theorem pre_le_normalizer {A B : Subgroup (Gbar K)}
    (h : A ≤ Subgroup.normalizer (B : Set (Gbar K))) :
    pre K A ≤ Subgroup.normalizer (pre K B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => pre_conj_mem K h hx hg, fun hg => ?_⟩
  have := pre_conj_mem K h ((pre K A).inv_mem hx) hg
  simpa [mul_assoc] using this

theorem isPGroup_zK (hZ : IsPGroup 2 ↥(Subgroup.center ↥K)) : IsPGroup 2 (zK K) := by
  intro z
  obtain ⟨hzK, hzc⟩ := (mem_zK K).1 z.2
  obtain ⟨k, hk⟩ := hZ ⟨⟨z, hzK⟩, hzc⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun w : ↥(Subgroup.center ↥K) => ((w : ↥K) : G)) hk
  simpa using this

theorem isPGroup_pre (hZ : IsPGroup 2 (zK K)) {B : Subgroup (Gbar K)} (hB : IsPGroup 2 B) :
    IsPGroup 2 (pre K B) := by
  intro g
  obtain ⟨hgN, hgB⟩ := (mem_pre K).1 g.2
  obtain ⟨a, ha⟩ := hB ⟨psi K ⟨g, hgN⟩, hgB⟩
  have ha' : (psi K ⟨g, hgN⟩) ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hz : (g : G) ^ 2 ^ a ∈ zK K := by
    have : psi K ((⟨g, hgN⟩ : ↥(nK K)) ^ 2 ^ a) = 1 := by rw [map_pow]; exact ha'
    exact (psi_eq_one K).1 this
  obtain ⟨b, hb⟩ := hZ ⟨_, hz⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have h1 : ((g : G) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  rw [← pow_mul, ← pow_add] at h1
  exact h1

theorem relIndex_pre (C₁ C₂ : Subgroup (Gbar K)) :
    (pre K C₁).relIndex (pre K C₂) = C₁.relIndex C₂ := by
  rw [pre, pre, Subgroup.relIndex_map_map_of_injective _ _ (nK K).subtype_injective,
    Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (psi_surjective K)]

theorem isSylowTwoOf_pre (hZ : IsPGroup 2 (zK K)) {X S : Subgroup (Gbar K)}
    (h : IsSylowTwoOf S X) : IsSylowTwoOf (pre K S) (pre K X) := by
  obtain ⟨hSX, hS2, hSi⟩ := h
  refine ⟨pre_mono K hSX, isPGroup_pre K hZ hS2, ?_⟩
  show ¬ 2 ∣ (pre K S).relIndex (pre K X)
  rw [relIndex_pre]
  exact hSi

theorem charTwo_pre [Finite G] (hZ : IsPGroup 2 (zK K)) {X : Subgroup (Gbar K)} (hX : CharTwo X) :
    CharTwo (pre K X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D' : Subgroup (Gbar K) := pCoreOf 2 X with hD'
  have hD'X : D' ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXD' : X ≤ Subgroup.normalizer (D' : Set (Gbar K)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hD'2 : IsPGroup 2 D' := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hle1 : pre K D' ≤ pCoreOf 2 (pre K X) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pre_mono K hD'X)
      (pre_le_normalizer K hXD') (isPGroup_pre K hZ hD'2)
  have hle2 : pCoreOf 2 (pre K X) ≤ pre K D' := by
    set E : Subgroup G := pCoreOf 2 (pre K X) with hE
    have hEX : E ≤ pre K X := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hEN : E ≤ nK K := hEX.trans (pre_le_nK K X)
    have hXE : pre K X ≤ Subgroup.normalizer (E : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hE2 : IsPGroup 2 E := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have himgX : img K E ≤ X := by
      have := img_mono K hEX
      rwa [img_pre] at this
    have himgN : X ≤ Subgroup.normalizer (img K E : Set (Gbar K)) := by
      have := img_le_normalizer K hXE
      rwa [img_pre] at this
    have hED : img K E ≤ D' :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 himgX himgN (img_isPGroup K hE2)
    exact (le_pre_img K hEN).trans (pre_mono K hED)
  have hcore : pCoreOf 2 (pre K X) = pre K D' := le_antisymm hle2 hle1
  intro c hc
  rw [hcore] at hc ⊢
  obtain ⟨hcX, hcC⟩ := hc
  obtain ⟨hcN, hcXbar⟩ := (mem_pre K).1 hcX
  refine (mem_pre K).2 ⟨hcN, ?_⟩
  apply hX
  refine ⟨hcXbar, ?_⟩
  show psi K ⟨c, hcN⟩ ∈ Subgroup.centralizer ((pCoreOf 2 X : Subgroup (Gbar K)) : Set (Gbar K))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ img K (pre K D') := by rwa [img_pre]
  obtain ⟨d, hdN, hdD, hdy⟩ := (mem_img K).1 hy'
  have := Subgroup.mem_centralizer_iff.1 hcC d hdD
  have h2 : psi K ⟨c, hcN⟩ * psi K ⟨d, hdN⟩ = psi K ⟨d, hdN⟩ * psi K ⟨c, hcN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg (psi K) (Subtype.ext this.symm)
  rw [← hdy]
  exact h2.symm

end CFSG.QuasithinUnique.A5.Kc3Cover
