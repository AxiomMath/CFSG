module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutInnerIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LCentral

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

section StepI

theorem conj_mem_of_centralizes_coatom {L K K₁ : Subgroup H} (hKL : K ≤ L)
    (hmax : ∀ X : Subgroup H, K ≤ X → X ≤ L → X = K ∨ X = L) (hK₁L : K₁ ≤ L) (hne : ¬ K₁ ≤ K)
    {u₁ : H} (hu₁ : u₁ ∈ K)
    (hn₁ : ∀ g ∈ centralizer ({u₁} : Set H), ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁)
    {g : H} (hg : g ∈ centralizer (K : Set H)) : ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
  have hgu₁ : g ∈ centralizer ({u₁} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hg u₁ hu₁).symm
  have hXL : K ⊔ K₁ ≤ L := sup_le hKL hK₁L
  have hX : K ⊔ K₁ = L := by
    rcases hmax (K ⊔ K₁) le_sup_left hXL with h | h
    · exact absurd (h ▸ le_sup_right) hne
    · exact h
  have hmap : (K ⊔ K₁).map (MulAut.conj g).toMonoidHom ≤ L := by
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨k, hk, rfl⟩
      have h1 : k * g = g * k := mem_centralizer_iff.1 hg k hk
      have h2 : (MulAut.conj g).toMonoidHom k = k := by
        show g * k * g⁻¹ = k
        rw [← h1]
        group
      rw [h2]
      exact hKL hk
    · rintro _ ⟨k, hk, rfl⟩
      exact hK₁L (hn₁ g hgu₁ k hk)
  intro x hx
  rw [← hX] at hx
  have := hmap ⟨x, hx, rfl⟩
  exact this

theorem mem_normalizer_of_centralizes_coatom {L K K₁ : Subgroup H} (hKL : K ≤ L)
    (hmax : ∀ X : Subgroup H, K ≤ X → X ≤ L → X = K ∨ X = L) (hK₁L : K₁ ≤ L) (hne : ¬ K₁ ≤ K)
    {u₁ : H} (hu₁ : u₁ ∈ K)
    (hn₁ : ∀ g ∈ centralizer ({u₁} : Set H), ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁)
    {g : H} (hg : g ∈ centralizer (K : Set H)) : g ∈ normalizer (L : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_of_centralizes_coatom hKL hmax hK₁L hne hu₁ hn₁ hg x hx
  · intro hx
    have h := conj_mem_of_centralizes_coatom hKL hmax hK₁L hne hu₁ hn₁
      ((centralizer (K : Set H)).inv_mem hg) _ hx
    simpa [mul_assoc] using h

theorem centralizer_le_sup_centralizer_of_coatom {L K K₁ : Subgroup H} (hKL : K ≤ L)
    (hmax : ∀ X : Subgroup H, K ≤ X → X ≤ L → X = K ∨ X = L) (hK₁L : K₁ ≤ L) (hne : ¬ K₁ ≤ K)
    {u₁ : H} (hu₁ : u₁ ∈ K)
    (hn₁ : ∀ g ∈ centralizer ({u₁} : Set H), ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁)
    (hN : normalizer (L : Set H) ≤ L ⊔ centralizer (L : Set H))
    (hCL : ∀ l ∈ L, (∀ k ∈ K, l * k = k * l) → l ∈ K) :
    centralizer (K : Set H) ≤ K ⊔ centralizer (L : Set H) := by
  intro g hg
  have hgN := hN (mem_normalizer_of_centralizes_coatom hKL hmax hK₁L hne hu₁ hn₁ hg)
  obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hgN
  have hlK : l ∈ K := by
    refine hCL l hl fun k hk => ?_
    have h1 : k * (l * z) = (l * z) * k := mem_centralizer_iff.1 hg k hk
    have h2 : k * z = z * k := mem_centralizer_iff.1 hz k (hKL hk)
    have h3 : k * l * z = l * k * z := by
      calc k * l * z = k * (l * z) := by rw [mul_assoc]
        _ = (l * z) * k := h1
        _ = l * (z * k) := by rw [mul_assoc]
        _ = l * (k * z) := by rw [h2]
        _ = l * k * z := by rw [mul_assoc]
    exact (mul_right_cancel h3).symm
  exact mul_mem (mem_sup_left hlK) (mem_sup_right hz)

theorem centralizer_inf_le_sup_centralizer {L : Subgroup H} {u l : H}
    (hmax : ∀ X : Subgroup H, L ⊓ centralizer ({u} : Set H) ≤ X → X ≤ L →
      X = L ⊓ centralizer ({u} : Set H) ∨ X = L)
    (hnorm : ∀ g ∈ centralizer ({u} : Set H), ∀ k ∈ L ⊓ centralizer ({u} : Set H),
      g * k * g⁻¹ ∈ L ⊓ centralizer ({u} : Set H))
    (hl : l ∈ L) (hlK : l * u * l⁻¹ ∈ L ⊓ centralizer ({u} : Set H))
    (hne : ¬ ∀ x ∈ L, x * (l * u * l⁻¹) = (l * u * l⁻¹) * x → x * u = u * x)
    (hN : normalizer (L : Set H) ≤ L ⊔ centralizer (L : Set H))
    (hCL : ∀ y ∈ L, (∀ k ∈ L ⊓ centralizer ({u} : Set H), y * k = k * y) →
      y ∈ L ⊓ centralizer ({u} : Set H)) :
    centralizer ((L ⊓ centralizer ({u} : Set H) : Subgroup H) : Set H) ≤
      (L ⊓ centralizer ({u} : Set H)) ⊔ centralizer (L : Set H) := by
  set K : Subgroup H := L ⊓ centralizer ({u} : Set H) with hK
  have hKL : K ≤ L := inf_le_left
  set K₁ : Subgroup H := K.map (MulAut.conj l).toMonoidHom with hK₁
  have hK₁L : K₁ ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact L.mul_mem (L.mul_mem hl (hKL hk)) (L.inv_mem hl)
  have hne₁ : ¬ K₁ ≤ K := by
    intro hle
    refine hne fun x hx hxu₁ => ?_
    have hyu : (l⁻¹ * x * l) * u = u * (l⁻¹ * x * l) := by
      calc l⁻¹ * x * l * u = l⁻¹ * (x * (l * u * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * u * l⁻¹) * x) * l := by rw [hxu₁]
        _ = u * (l⁻¹ * x * l) := by group
    have hy : l⁻¹ * x * l ∈ K :=
      ⟨L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl, mem_centralizer_singleton_iff.2 hyu⟩
    have hxK₁ : x ∈ K₁ := ⟨l⁻¹ * x * l, hy, by
      show l * (l⁻¹ * x * l) * l⁻¹ = x
      group⟩
    exact mem_centralizer_singleton_iff.1 (hle hxK₁).2
  have hn₁ : ∀ g ∈ centralizer ({l * u * l⁻¹} : Set H), ∀ k ∈ K₁, g * k * g⁻¹ ∈ K₁ := by
    intro g hg k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    have hg₁ : g * (l * u * l⁻¹) = (l * u * l⁻¹) * g := mem_centralizer_singleton_iff.1 hg
    have hg' : l⁻¹ * g * l ∈ centralizer ({u} : Set H) := by
      refine mem_centralizer_singleton_iff.2 ?_
      calc l⁻¹ * g * l * u = l⁻¹ * (g * (l * u * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * u * l⁻¹) * g) * l := by rw [hg₁]
        _ = u * (l⁻¹ * g * l) := by group
    refine ⟨(l⁻¹ * g * l) * k₀ * (l⁻¹ * g * l)⁻¹, hnorm _ hg' k₀ hk₀, ?_⟩
    show l * ((l⁻¹ * g * l) * k₀ * (l⁻¹ * g * l)⁻¹) * l⁻¹ =
      g * (l * k₀ * l⁻¹) * g⁻¹
    group
  exact centralizer_le_sup_centralizer_of_coatom hKL hmax hK₁L hne₁ hlK hn₁ hN hCL

end StepI

section Fusion

variable [Finite H]

theorem exists_involution_of_fusion {L : Subgroup H} {t u a : H} (hs : Setting612 H L t)
    (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) (ha : a ∈ L) (hau : a * u = u * a)
    (c : H) (hc : c * t * c⁻¹ = t * a) :
    ∃ p ∈ L, p * p = 1 ∧ p ≠ 1 ∧
      2 * Nat.card ↥(L ⊓ centralizer ({p} : Set H)) ≤
        Nat.card ↥(centralizer ({u} : Set H) ⊓ centralizer ({t * a} : Set H)) := by
  classical
  have hLt : ∀ x ∈ L, x * t = t * x := fun x hx => hs.comm_of_mem hx
  have hut : u * t = t * u := hLt u hu
  obtain ⟨e, he⟩ : ∃ e : H, e = c⁻¹ * u * c := ⟨_, rfl⟩
  have hue : u * (t * a) = (t * a) * u := by
    calc u * (t * a) = (u * t) * a := by rw [mul_assoc]
      _ = (t * u) * a := by rw [hut]
      _ = t * (u * a) := by rw [mul_assoc]
      _ = t * (a * u) := by rw [hau.symm]
      _ = (t * a) * u := by rw [← mul_assoc]
  have hct : c * t = (t * a) * c := by
    calc c * t = c * t * c⁻¹ * c := by group
      _ = (t * a) * c := by rw [hc]
  have ht' : c⁻¹ * (t * a) * c = t := by
    calc c⁻¹ * (t * a) * c = c⁻¹ * ((t * a) * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * t) := by rw [hct]
      _ = t := by group
  have het : e * t = t * e := by
    calc e * t = c⁻¹ * u * (c * t) := by rw [he]; group
      _ = c⁻¹ * u * ((t * a) * c) := by rw [hct]
      _ = c⁻¹ * (u * (t * a)) * c := by group
      _ = c⁻¹ * ((t * a) * u) * c := by rw [hue]
      _ = (c⁻¹ * (t * a) * c) * (c⁻¹ * u * c) := by group
      _ = t * e := by rw [ht', ← he]
  have hee : e * e = 1 := by
    calc e * e = c⁻¹ * (u * u) * c := by rw [he]; group
      _ = 1 := by rw [hu2]; group
  have hue_eq : u = c * e * c⁻¹ := by rw [he]; group
  have hta_eq : t * a = c * t * c⁻¹ := hc.symm
  obtain ⟨p, hp, hpe⟩ := hs.exists_eq_mul
    (Subgroup.mem_centralizer_singleton_iff.2 het : e ∈ centralizer ({t} : Set H))
  have hpt : p * t = t * p := hLt p hp
  have hp2 : p * p = 1 := by
    rcases hpe with h | h
    · rw [← h]; exact hee
    · have : e * e = p * p := by
        rw [h]
        calc p * t * (p * t) = p * (t * p) * t := by group
          _ = p * (p * t) * t := by rw [← hpt]
          _ = p * p * (t * t) := by group
          _ = p * p := by rw [hs.t_sq, mul_one]
      rw [← this]; exact hee
  have hp1 : p ≠ 1 := by
    intro h1
    rcases hpe with h | h
    · rw [h1] at h
      apply hu1
      rw [hue_eq, h]
      group
    · rw [h1, one_mul] at h
      apply hs.not_mem_of
      have hu_eq : u = t * a := by rw [hue_eq, h, ← hta_eq]
      have : t = u * a⁻¹ := by rw [hu_eq]; group
      rw [this]
      exact L.mul_mem hu (L.inv_mem ha)
  refine ⟨p, hp, hp2, hp1, ?_⟩
  set P : Subgroup H := L ⊓ centralizer ({p} : Set H) with hP
  set X : Subgroup H := centralizer ({u} : Set H) ⊓ centralizer ({t * a} : Set H) with hX
  set Y : Set H := (P : Set H) ∪ (fun y => t * y) '' (P : Set H) with hY
  have hcomm_t_e : Commute t e := het.symm
  have hcomm_e : ∀ w ∈ Y, Commute w e := by
    intro w hw
    have hyP : ∀ y ∈ P, Commute y e := by
      intro y hy
      have hyp : Commute y p := (Subgroup.mem_centralizer_singleton_iff.1 hy.2)
      have hyt : Commute y t := hLt y hy.1
      rcases hpe with h | h
      · rw [h]; exact hyp
      · rw [h]; exact hyp.mul_right hyt
    rcases hw with hw | ⟨y, hy, rfl⟩
    · exact hyP w hw
    · exact hcomm_t_e.mul_left (hyP y hy)
  have hcomm_t : ∀ w ∈ Y, Commute w t := by
    intro w hw
    rcases hw with hw | ⟨y, hy, rfl⟩
    · exact hLt w hw.1
    · exact (Commute.refl t).mul_left (hLt y hy.1)
  have hYsub : (fun w : H => c * w * c⁻¹) '' Y ⊆ (X : Set H) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwe : w * e = e * w := hcomm_e w hw
    have hwt : w * t = t * w := hcomm_t w hw
    have h1 : c * w * c⁻¹ * u = u * (c * w * c⁻¹) := by
      rw [hue_eq]
      calc c * w * c⁻¹ * (c * e * c⁻¹) = c * (w * e) * c⁻¹ := by group
        _ = c * (e * w) * c⁻¹ := by rw [hwe]
        _ = c * e * c⁻¹ * (c * w * c⁻¹) := by group
    have h2 : c * w * c⁻¹ * (t * a) = (t * a) * (c * w * c⁻¹) := by
      rw [hta_eq]
      calc c * w * c⁻¹ * (c * t * c⁻¹) = c * (w * t) * c⁻¹ := by group
        _ = c * (t * w) * c⁻¹ := by rw [hwt]
        _ = c * t * c⁻¹ * (c * w * c⁻¹) := by group
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 h1,
      Subgroup.mem_centralizer_singleton_iff.2 h2⟩
  have hP_fin : (P : Set H).Finite := Set.toFinite _
  have hdisj : Disjoint (P : Set H) ((fun y => t * y) '' (P : Set H)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨y', hy', rfl⟩
    apply hs.not_mem_of
    have := L.mul_mem hy.1 (L.inv_mem hy'.1)
    simpa using this
  have hYcard : Y.ncard = 2 * (P : Set H).ncard := by
    rw [hY, Set.ncard_union_eq hdisj hP_fin (hP_fin.image _),
      Set.ncard_image_of_injective _ (mul_right_injective t)]
    ring
  have hinj : Function.Injective (fun w : H => c * w * c⁻¹) := by
    intro x y h
    simpa using h
  have hPc : Nat.card ↥P = (P : Set H).ncard := Nat.card_coe_set_eq (P : Set H)
  have hXc : Nat.card ↥X = (X : Set H).ncard := Nat.card_coe_set_eq (X : Set H)
  calc 2 * Nat.card ↥P = Y.ncard := by rw [hPc, hYcard]
    _ = ((fun w : H => c * w * c⁻¹) '' Y).ncard := (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (X : Set H).ncard := Set.ncard_le_ncard hYsub (Set.toFinite _)
    _ = Nat.card ↥X := hXc.symm

theorem card_centralizer_pair_le {L : Subgroup H} {t u a : H} (hs : Setting612 H L t)
    (hbal : centralizer (L : Set H) ⊓ centralizer ({t} : Set H) = zpowers t)
    (hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1) (ha : a ∈ L)
    (hCK : centralizer ((L ⊓ centralizer ({u} : Set H) : Subgroup H) : Set H) ≤
      (L ⊓ centralizer ({u} : Set H)) ⊔ centralizer (L : Set H))
    (hnorm : ∀ g ∈ centralizer ({u} : Set H), ∀ k ∈ L ⊓ centralizer ({u} : Set H),
      g * k * g⁻¹ ∈ L ⊓ centralizer ({u} : Set H))
    (hInn : (AutInner.innerAut ↥(L ⊓ centralizer ({u} : Set H))).index ≤ 2) :
    Nat.card ↥(centralizer ({u} : Set H) ⊓ centralizer ({t * a} : Set H)) ≤
      4 * Nat.card ↥(L ⊓ centralizer ({u} : Set H) ⊓ centralizer ({a} : Set H)) := by
  classical
  set K : Subgroup H := L ⊓ centralizer ({u} : Set H) with hKdef
  set C : Subgroup H := centralizer ({u} : Set H) with hCdef
  set s : H := t * a with hsdef
  set X : Subgroup H := C ⊓ centralizer ({s} : Set H) with hXdef
  set A : Subgroup H := K ⊓ centralizer ({a} : Set H) with hAdef
  have hKL : K ≤ L := inf_le_left
  have hLt : ∀ x ∈ L, x * t = t * x := fun x hx => hs.comm_of_mem hx
  have hCN : C ≤ normalizer (K : Set H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hnorm g hg k hk
    · intro hk
      have h := hnorm g⁻¹ (C.inv_mem hg) _ hk
      simpa [mul_assoc] using h
  let φ : ↥C →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hCN)
  let I : Subgroup ↥C := (AutInner.innerAut ↥K).comap φ
  have hI : I.index ≤ 2 := AutInner.index_comap_innerAut_le_two hInn φ
  set M₁ : Subgroup H := I.map C.subtype with hM₁
  have hM₁rel : M₁.relIndex C = I.index := by
    unfold Subgroup.relIndex
    rw [hM₁]
    exact congrArg Subgroup.index (Subgroup.comap_map_eq_self_of_injective C.subtype_injective I)
  have hXC : X ≤ C := inf_le_left
  have hrel : M₁.relIndex X ≤ 2 := by
    have hne : M₁.relIndex C ≠ 0 := by
      rw [hM₁rel]
      exact Subgroup.index_ne_zero_of_finite
    exact (Subgroup.relIndex_le_of_le_right hXC hne).trans (hM₁rel ▸ hI)
  have hcard1 : Nat.card ↥X ≤ 2 * Nat.card ↥(M₁ ⊓ X) := by
    calc Nat.card ↥X = M₁.relIndex X * Nat.card ↥(M₁ ⊓ X) := (Subgroup.relIndex_mul_card M₁ X).symm
      _ ≤ 2 * Nat.card ↥(M₁ ⊓ X) := Nat.mul_le_mul_right _ hrel
  have key : ∀ m ∈ M₁ ⊓ X, m ∈ A ∨ ∃ y ∈ A, m = t * y := by
    intro m hm
    obtain ⟨hmM, hmX⟩ := hm
    obtain ⟨c₀, hc₀, hc₀m⟩ := Subgroup.mem_map.1 hmM
    have hc₀m' : (c₀ : H) = m := hc₀m
    obtain ⟨k, hk⟩ : ∃ k : ↥K, MulAut.conj k = φ c₀ := Subgroup.mem_comap.1 hc₀
    have hconj : ∀ x ∈ K, (c₀ : H) * x * (c₀ : H)⁻¹ = (k : H) * x * (k : H)⁻¹ :=
      (normalizerMonoidHom_eq_conj_iff (hCN c₀.2) k).1 hk.symm
    have hz₀ : (k : H)⁻¹ * (c₀ : H) ∈ centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := hconj x hx
      calc x * ((k : H)⁻¹ * c₀) = (k : H)⁻¹ * ((k : H) * x * (k : H)⁻¹) * c₀ := by group
        _ = (k : H)⁻¹ * ((c₀ : H) * x * (c₀ : H)⁻¹) * c₀ := by rw [h]
        _ = ((k : H)⁻¹ * c₀) * x := by group
    obtain ⟨k₂, hk₂, z, hz, hz₀eq⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := K) (B := centralizer (L : Set H))
      (Subgroup.centralizer_le (fun x hx => hKL hx)) (hCK hz₀)
    have hm : m = ((k : H) * k₂) * z := by
      rw [← hc₀m']
      calc (c₀ : H) = (k : H) * ((k : H)⁻¹ * c₀) := by group
        _ = (k : H) * (k₂ * z) := by rw [hz₀eq]
        _ = ((k : H) * k₂) * z := by rw [mul_assoc]
    have hk'K : (k : H) * k₂ ∈ K := K.mul_mem k.2 hk₂
    have hk'L : (k : H) * k₂ ∈ L := hKL hk'K
    set k' : H := (k : H) * k₂ with hk'
    have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mem_centralizer_iff.1 hz x hx
    have hms : m * s = s * m := Subgroup.mem_centralizer_singleton_iff.1 hmX.2
    have hza : z * a * z⁻¹ = a := by
      calc z * a * z⁻¹ = a * z * z⁻¹ := by rw [← hzL a ha]
        _ = a := by group
    have hwL : ∀ x ∈ L, x * (z * t * z⁻¹) = (z * t * z⁻¹) * x := by
      intro x hx
      have hxz : Commute x z := hzL x hx
      have hxt : Commute x t := hLt x hx
      exact (hxz.mul_right hxt).mul_right hxz.inv_right
    have hk'w : k' * (z * t * z⁻¹) = (z * t * z⁻¹) * k' := hwL k' hk'L
    have hwa : (k' * z) * (t * a) * (k' * z)⁻¹ = (z * t * z⁻¹) * (k' * a * k'⁻¹) := by
      calc (k' * z) * (t * a) * (k' * z)⁻¹
          = k' * ((z * t * z⁻¹) * (z * a * z⁻¹)) * k'⁻¹ := by group
        _ = k' * ((z * t * z⁻¹) * a) * k'⁻¹ := by rw [hza]
        _ = (k' * (z * t * z⁻¹)) * a * k'⁻¹ := by group
        _ = ((z * t * z⁻¹) * k') * a * k'⁻¹ := by rw [hk'w]
        _ = (z * t * z⁻¹) * (k' * a * k'⁻¹) := by group
    have hsm : (k' * z) * (t * a) * (k' * z)⁻¹ = t * a := by
      have : (k' * z) * (t * a) = (t * a) * (k' * z) := by rw [← hm]; exact hms
      rw [this]
      group
    have hwa' : (z * t * z⁻¹) * (k' * a * k'⁻¹) = t * a := by rw [← hwa]; exact hsm
    have hx_eq : t⁻¹ * (z * t * z⁻¹) = a * (k' * a * k'⁻¹)⁻¹ := by
      have h1 : z * t * z⁻¹ = t * a * (k' * a * k'⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact hwa'
      rw [h1]
      group
    have hxL : a * (k' * a * k'⁻¹)⁻¹ ∈ L := by
      refine L.mul_mem ha (L.inv_mem ?_)
      exact L.mul_mem (L.mul_mem hk'L ha) (L.inv_mem hk'L)
    have hxc : ∀ y ∈ L, (a * (k' * a * k'⁻¹)⁻¹) * y = y * (a * (k' * a * k'⁻¹)⁻¹) := by
      intro y hy
      rw [← hx_eq]
      have hyt : Commute y t := hLt y hy
      have hyw : Commute y (z * t * z⁻¹) := hwL y hy
      exact (hyt.inv_right.mul_right hyw).symm
    have hx1 : a * (k' * a * k'⁻¹)⁻¹ = 1 := hZ _ hxL hxc
    have haa : k' * a * k'⁻¹ = a := (mul_inv_eq_one.1 hx1).symm
    have hwt : z * t * z⁻¹ = t := by
      have h2 : t⁻¹ * (z * t * z⁻¹) = 1 := by rw [hx_eq]; exact hx1
      exact (inv_mul_eq_one.1 h2).symm
    have hk'a : k' * a = a * k' := by
      calc k' * a = (k' * a * k'⁻¹) * k' := by group
        _ = a * k' := by rw [haa]
    have hzt : z * t = t * z := by
      calc z * t = (z * t * z⁻¹) * z := by group
        _ = t * z := by rw [hwt]
    have hzmem : z ∈ zpowers t := by
      rw [← hbal]
      exact ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 hzt⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hzmem
    have hkA : k' ∈ A := ⟨hk'K, Subgroup.mem_centralizer_singleton_iff.2 hk'a⟩
    rcases zpow_eq_one_or_self_of_orderOf_eq_two hs.t_order j with h1 | h1
    · left
      have hz1 : z = 1 := by rw [← hj, h1]
      rw [hm, hz1, mul_one]
      exact hkA
    · right
      refine ⟨k', hkA, ?_⟩
      have hzt' : z = t := by rw [← hj, h1]
      rw [hm, hzt']
      exact hLt k' hk'L
  have hsub : ((M₁ ⊓ X : Subgroup H) : Set H) ⊆
      (A : Set H) ∪ (fun y => t * y) '' (A : Set H) := by
    intro m hm
    rcases key m hm with h | ⟨y, hy, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, rfl⟩
  have hcard2 : Nat.card ↥(M₁ ⊓ X) ≤ 2 * Nat.card ↥A := by
    have h1 : Nat.card ↥(M₁ ⊓ X) = ((M₁ ⊓ X : Subgroup H) : Set H).ncard :=
      Nat.card_coe_set_eq _
    have h2 : Nat.card ↥A = (A : Set H).ncard := Nat.card_coe_set_eq _
    rw [h1, h2]
    calc ((M₁ ⊓ X : Subgroup H) : Set H).ncard ≤
          ((A : Set H) ∪ (fun y => t * y) '' (A : Set H)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (A : Set H).ncard + ((fun y => t * y) '' (A : Set H)).ncard := Set.ncard_union_le _ _
      _ = 2 * (A : Set H).ncard := by
          rw [Set.ncard_image_of_injective _ (mul_right_injective t)]
          ring
  calc Nat.card ↥X ≤ 2 * Nat.card ↥(M₁ ⊓ X) := hcard1
    _ ≤ 2 * (2 * Nat.card ↥A) := Nat.mul_le_mul_left _ hcard2
    _ = 4 * Nat.card ↥A := by ring

theorem fusion_centralizer_le {L : Subgroup H} {t u a : H} (hs : Setting612 H L t)
    (hbal : centralizer (L : Set H) ⊓ centralizer ({t} : Set H) = zpowers t)
    (hZ : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1)
    (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) (ha : a ∈ L) (hau : a * u = u * a)
    (hCK : centralizer ((L ⊓ centralizer ({u} : Set H) : Subgroup H) : Set H) ≤
      (L ⊓ centralizer ({u} : Set H)) ⊔ centralizer (L : Set H))
    (hnorm : ∀ g ∈ centralizer ({u} : Set H), ∀ k ∈ L ⊓ centralizer ({u} : Set H),
      g * k * g⁻¹ ∈ L ⊓ centralizer ({u} : Set H))
    (hInn : (AutInner.innerAut ↥(L ⊓ centralizer ({u} : Set H))).index ≤ 2)
    (hconj : IsConj t (t * a)) :
    ∃ p ∈ L, p * p = 1 ∧ p ≠ 1 ∧
      Nat.card ↥(L ⊓ centralizer ({p} : Set H)) ≤
        2 * Nat.card ↥(L ⊓ centralizer ({u} : Set H) ⊓ centralizer ({a} : Set H)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨p, hp, hp2, hp1, hlow⟩ := exists_involution_of_fusion hs hu hu2 hu1 ha hau c hc
  have hup := card_centralizer_pair_le hs hbal hZ ha hCK hnorm hInn
  exact ⟨p, hp, hp2, hp1, by omega⟩

end Fusion

end CFSG.EvenSporadicStandard.Induction
