module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def bar (R K : Subgroup G) [(K.subgroupOf R).Normal] (X : Subgroup G) :
    Subgroup (↥R ⧸ K.subgroupOf R) :=
  (X.subgroupOf R).map (QuotientGroup.mk' (K.subgroupOf R))

@[expose] noncomputable def barPre (R K : Subgroup G) [(K.subgroupOf R).Normal] (A : Subgroup G)
    (E : Subgroup (↥R ⧸ K.subgroupOf R)) : Subgroup G :=
  A ⊓ (E.comap (QuotientGroup.mk' (K.subgroupOf R))).map R.subtype

variable {R K : Subgroup G} [(K.subgroupOf R).Normal]

private theorem relIndex_mul_card_aux {H K' : Subgroup G} (h : H ≤ K') :
    H.relIndex K' * Nat.card H = Nat.card K' := by
  have h1 : Nat.card (H.subgroupOf K') = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have h2 : Nat.card (H.subgroupOf K') * (H.subgroupOf K').index = Nat.card K' :=
    Subgroup.card_mul_index (H.subgroupOf K')
  rw [h1] at h2
  unfold Subgroup.relIndex
  rw [mul_comm]
  exact h2

theorem mk_mem_bar {X : Subgroup G} {r : ↥R} (hr : (r : G) ∈ X) :
    (QuotientGroup.mk' (K.subgroupOf R) r) ∈ bar R K X :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)

theorem bar_mono {X Y : Subgroup G} (h : X ≤ Y) : bar R K X ≤ bar R K Y := by
  unfold bar
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono R h)

theorem card_bar_dvd {X : Subgroup G} (hXR : X ≤ R) : Nat.card (bar R K X) ∣ Nat.card X := by
  have h1 : Nat.card (X.subgroupOf R) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXR).toEquiv
  have h2 : Nat.card ((X.subgroupOf R).map (QuotientGroup.mk' (K.subgroupOf R))) ∣
      Nat.card (X.subgroupOf R) := Subgroup.card_map_dvd (X.subgroupOf R) _
  rw [h1] at h2
  exact h2

theorem card_bar {X : Subgroup G} (hXR : X ≤ R) (hKX : K ≤ X) :
    Nat.card (bar R K X) = K.relIndex X := by
  let f : ↥X →* ↥(bar R K X) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (K.subgroupOf R)).comp (Subgroup.inclusion hXR))
      (bar R K X) (fun x => mk_mem_bar (r := Subgroup.inclusion hXR x) x.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩, rfl⟩
  have hone : ∀ r : ↥R, QuotientGroup.mk' (K.subgroupOf R) r = 1 ↔ (r : G) ∈ K :=
    fun r => (QuotientGroup.eq_one_iff r).trans Subgroup.mem_subgroupOf.symm
  have hker : f.ker = K.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (hone (Subgroup.inclusion hXR x)).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((hone (Subgroup.inclusion hXR x)).mpr hx)
  have h5 : ((⊥ : Subgroup ↥(bar R K X)).comap f).index = (⊥ : Subgroup ↥(bar R K X)).index :=
    Subgroup.index_comap_of_surjective (⊥ : Subgroup ↥(bar R K X)) hsurj
  have h4 : (K.subgroupOf X).index = Nat.card (bar R K X) := by
    rw [← hker]
    exact h5.trans Subgroup.index_bot
  exact h4.symm

theorem odd_card_bar {X : Subgroup G} (hXR : X ≤ R) (hKX : K ≤ X) (h : ¬ 2 ∣ K.relIndex X) :
    Odd (Nat.card (bar R K X)) := by
  rw [card_bar hXR hKX]
  exact Nat.odd_iff.mpr (by omega)

theorem isElemAbelian_bar {X : Subgroup G} (hX : IsElemAbelian 2 X) :
    IsElemAbelian 2 (bar R K X) := by
  unfold bar
  exact (hX.subgroupOf R).map _

theorem isPGroup_bar {X : Subgroup G} (hX : IsPGroup 2 X) : IsPGroup 2 (bar R K X) := by
  unfold bar
  exact (IsPGroup.comap_of_injective hX R.subtype Subtype.val_injective).map _

theorem mk_commute_iff (r s : ↥R) :
    QuotientGroup.mk' (K.subgroupOf R) r * QuotientGroup.mk' (K.subgroupOf R) s =
        QuotientGroup.mk' (K.subgroupOf R) s * QuotientGroup.mk' (K.subgroupOf R) r ↔
      (r : G) * s * (r : G)⁻¹ * (s : G)⁻¹ ∈ K := by
  have hN : (K.subgroupOf R).Normal := inferInstance
  have hu : (r * s * r⁻¹ * s⁻¹ : ↥R) ∈ K.subgroupOf R ↔
      (r : G) * s * (r : G)⁻¹ * (s : G)⁻¹ ∈ K := by
    rw [Subgroup.mem_subgroupOf]
    simp
  have e1 : QuotientGroup.mk' (K.subgroupOf R) r * QuotientGroup.mk' (K.subgroupOf R) s =
      QuotientGroup.mk' (K.subgroupOf R) (r * s) := (map_mul _ r s).symm
  have e2 : QuotientGroup.mk' (K.subgroupOf R) s * QuotientGroup.mk' (K.subgroupOf R) r =
      QuotientGroup.mk' (K.subgroupOf R) (s * r) := (map_mul _ s r).symm
  have key : ∀ g : ↥R, (r * s)⁻¹ * (s * r) ∈ K.subgroupOf R ↔
      g * ((r * s)⁻¹ * (s * r)) * g⁻¹ ∈ K.subgroupOf R := by
    intro g
    constructor
    · intro h
      exact hN.conj_mem _ h g
    · intro h
      have h' := hN.conj_mem _ h g⁻¹
      have e5 : g⁻¹ * (g * ((r * s)⁻¹ * (s * r)) * g⁻¹) * g⁻¹⁻¹ = (r * s)⁻¹ * (s * r) := by
        group
      rwa [e5] at h'
  have e3 : r * s * ((r * s)⁻¹ * (s * r)) * (r * s)⁻¹ = s * r * s⁻¹ * r⁻¹ := by group
  have e4 : r * s * r⁻¹ * s⁻¹ = (s * r * s⁻¹ * r⁻¹)⁻¹ := by group
  rw [e1, e2, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← hu,
    key (r * s), e3, e4, Subgroup.inv_mem_iff]

theorem mk_eq_one_iff (r : ↥R) : QuotientGroup.mk' (K.subgroupOf R) r = 1 ↔ (r : G) ∈ K :=
  (QuotientGroup.eq_one_iff r).trans Subgroup.mem_subgroupOf.symm

theorem bar_le_normalizer {X Y : Subgroup G} (hXR : X ≤ R) (hYR : Y ≤ R)
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    bar R K X ≤ Subgroup.normalizer (bar R K Y : Set (↥R ⧸ K.subgroupOf R)) := by
  have help : ∀ x : ↥R, (x : G) ∈ X → ∀ p ∈ bar R K Y,
      QuotientGroup.mk' (K.subgroupOf R) x * p * (QuotientGroup.mk' (K.subgroupOf R) x)⁻¹ ∈
        bar R K Y := by
    intro x hx p hp
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hN : (y : G) ∈ Y ↔ (x : G) * (y : G) * (x : G)⁻¹ ∈ Y :=
      Subgroup.mem_normalizer_iff.mp (h hx) (y : G)
    have hxy : ((x * y * x⁻¹ : ↥R) : G) ∈ Y := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hN.mp hyY
    have e : QuotientGroup.mk' (K.subgroupOf R) x * QuotientGroup.mk' (K.subgroupOf R) y *
        (QuotientGroup.mk' (K.subgroupOf R) x)⁻¹ =
          QuotientGroup.mk' (K.subgroupOf R) (x * y * x⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact mk_mem_bar hxy
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact help x hxX p
  · intro hp
    have hx' : ((x⁻¹ : ↥R) : G) ∈ X := by
      rw [Subgroup.coe_inv]
      exact X.inv_mem hxX
    have h2 := help x⁻¹ hx' _ hp
    rw [map_inv] at h2
    have e : ∀ a p : ↥R ⧸ K.subgroupOf R, a⁻¹ * (a * p * a⁻¹) * a⁻¹⁻¹ = p := fun a p => by
      group
    rwa [e] at h2

theorem map_conj_bar {X : Subgroup G} (hXR : X ≤ R) (s : ↥R) :
    (bar R K X).map (MulAut.conj (QuotientGroup.mk' (K.subgroupOf R) s)).toMonoidHom =
      bar R K (X.map (MulAut.conj (s : G)).toMonoidHom) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hp
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hmem : ((s * x * s⁻¹ : ↥R) : G) ∈ X.map (MulAut.conj (s : G)).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(x : G), hxX, ?_⟩
      simp [MulAut.conj_apply]
    have e : (MulAut.conj (QuotientGroup.mk' (K.subgroupOf R) s)).toMonoidHom
        (QuotientGroup.mk' (K.subgroupOf R) x) =
          QuotientGroup.mk' (K.subgroupOf R) (s * x * s⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rw [e]
    exact mk_mem_bar hmem
  · intro hq
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hr)
    have hyR : y ∈ R := hXR hy
    have hrs : s * ⟨y, hyR⟩ * s⁻¹ = r := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] at hyr ⊢
      exact hyr
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (K.subgroupOf R) ⟨y, hyR⟩,
      mk_mem_bar (r := ⟨y, hyR⟩) hy, ?_⟩
    rw [← hrs]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem barPre_le (A : Subgroup G) (E : Subgroup (↥R ⧸ K.subgroupOf R)) : barPre R K A E ≤ A := by
  unfold barPre
  exact inf_le_left

theorem mem_barPre_iff {A : Subgroup G} {E : Subgroup (↥R ⧸ K.subgroupOf R)} {a : G} :
    a ∈ barPre R K A E ↔ a ∈ A ∧ ∃ ha : a ∈ R, QuotientGroup.mk' (K.subgroupOf R) ⟨a, ha⟩ ∈ E := by
  unfold barPre
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hA, x, hx, hxa⟩
    subst hxa
    exact ⟨hA, x.2, hx⟩
  · rintro ⟨hA, ha, hE⟩
    exact ⟨hA, ⟨a, ha⟩, hE, rfl⟩

theorem card_le_two_mul_card_barPre {A : Subgroup G} (hAR : A ≤ R)
    {E : Subgroup (↥R ⧸ K.subgroupOf R)} (hE : E ≤ bar R K A)
    (hcard : Nat.card (bar R K A) ≤ 2 * Nat.card E) :
    Nat.card A ≤ 2 * Nat.card (barPre R K A E) := by
  have hPA : barPre R K A E ≤ A := barPre_le A E
  let f : ↥A →* ↥(bar R K A) :=
    MonoidHom.codRestrict ((QuotientGroup.mk' (K.subgroupOf R)).comp (Subgroup.inclusion hAR))
      (bar R K A) (fun x => mk_mem_bar (r := Subgroup.inclusion hAR x) x.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨(r : G), Subgroup.mem_subgroupOf.mp hr⟩, rfl⟩
  have hcomap : (E.subgroupOf (bar R K A)).comap f = (barPre R K A E).subgroupOf A := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_barPre_iff]
    constructor
    · intro h
      exact ⟨x.2, hAR x.2, h⟩
    · rintro ⟨_, _, h⟩
      exact h
  have step2 : (barPre R K A E).relIndex A = E.relIndex (bar R K A) := by
    unfold Subgroup.relIndex
    rw [← hcomap]
    exact Subgroup.index_comap_of_surjective (E.subgroupOf (bar R K A)) hsurj
  have step1 := relIndex_mul_card_aux hPA
  have step3 := relIndex_mul_card_aux hE
  have hpos : 0 < Nat.card E := Nat.card_pos
  have step4 : E.relIndex (bar R K A) ≤ 2 := by
    have h5 : E.relIndex (bar R K A) * Nat.card E ≤ 2 * Nat.card E := by
      rw [step3]
      exact hcard
    exact Nat.le_of_mul_le_mul_right h5 hpos
  rw [← step1, step2]
  exact Nat.mul_le_mul step4 le_rfl

theorem exists_odd_pow (g : ↥R) (hg : Odd (orderOf (QuotientGroup.mk' (K.subgroupOf R) g))) :
    ∃ k : ℕ, Odd (orderOf ((g : G) ^ k)) ∧
      QuotientGroup.mk' (K.subgroupOf R) (g ^ k) = QuotientGroup.mk' (K.subgroupOf R) g := by
  obtain ⟨a, b, hb, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (QuotientGroup.mk' (K.subgroupOf R) g)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hg)
  have hc : ∃ c : ℕ, (QuotientGroup.mk' (K.subgroupOf R) g) ^ (2 ^ a * c) =
      QuotientGroup.mk' (K.subgroupOf R) g := by
    rcases Nat.lt_or_ge 1 (orderOf (QuotientGroup.mk' (K.subgroupOf R) g)) with h1 | h1
    · obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
      exact ⟨c, by
        rw [← pow_mod_orderOf (QuotientGroup.mk' (K.subgroupOf R) g) (2 ^ a * c), hc, pow_one]⟩
    · have h1' : orderOf (QuotientGroup.mk' (K.subgroupOf R) g) = 1 := by
        have := hg.pos
        omega
      exact ⟨1, by rw [orderOf_eq_one_iff.mp h1', one_pow]⟩
  obtain ⟨c, hcq⟩ := hc
  refine ⟨2 ^ a * c, ?_, ?_⟩
  · have hyb : (g ^ (2 ^ a * c)) ^ b = 1 := by
      rw [← pow_mul, show 2 ^ a * c * b = orderOf g * c by (rw [hm]; ring), pow_mul,
        pow_orderOf_eq_one, one_pow]
    rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hb (orderOf_dvd_of_pow_eq_one hyb)
  · rw [map_pow]
    exact hcq

theorem exists_odd_lift {L : Subgroup G} (hLR : L ≤ R) {q : ↥R ⧸ K.subgroupOf R}
    (hq : q ∈ bar R K L) (hqo : Odd (orderOf q)) :
    ∃ y : ↥R, (y : G) ∈ L ∧ Odd (orderOf (y : G)) ∧ QuotientGroup.mk' (K.subgroupOf R) y = q := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
  obtain ⟨k, hk1, hk2⟩ := exists_odd_pow g hqo
  refine ⟨g ^ k, ?_, ?_, hk2⟩
  · rw [Subgroup.coe_pow]
    exact L.pow_mem (Subgroup.mem_subgroupOf.mp hg) k
  · rw [Subgroup.coe_pow]
    exact hk1

theorem exists_pPow_lift {L : Subgroup G} (hLR : L ≤ R) {p : ℕ} (hp : p.Prime)
    {q : ↥R ⧸ K.subgroupOf R} (hq : q ∈ bar R K L) (hqo : orderOf q = p) :
    ∃ y : ↥R, (y : G) ∈ L ∧ IsPGroup p (Subgroup.zpowers (y : G)) ∧
      QuotientGroup.mk' (K.subgroupOf R) y = q := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
  have hgL : (g : G) ∈ L := Subgroup.mem_subgroupOf.mp hg
  obtain ⟨a, b, hpb, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hcop : Nat.Coprime b p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hqc : (QuotientGroup.mk' (K.subgroupOf R) g) ^ (b * c) =
      QuotientGroup.mk' (K.subgroupOf R) g := by
    rw [← pow_mod_orderOf (QuotientGroup.mk' (K.subgroupOf R) g) (b * c), hqo, hc, pow_one]
  have hpow : (g ^ (b * c)) ^ (p ^ a) = 1 := by
    rw [← pow_mul, show b * c * p ^ a = orderOf g * c by (rw [hm]; ring), pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hdvd : orderOf ((g ^ (b * c) : ↥R) : G) ∣ p ^ a := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨g ^ (b * c), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact L.pow_mem hgL _
  · have hcard : Nat.card (Subgroup.zpowers ((g ^ (b * c) : ↥R) : G)) = p ^ k := by
      rw [Nat.card_zpowers]
      exact hk
    exact IsPGroup.of_card hcard
  · rw [map_pow]
    exact hqc

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
