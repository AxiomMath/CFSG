module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma410

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X]

structure IsBeta411 (t : X) (L S : Subgroup X) (w z : X) (V : Subgroup X) (β : X) : Prop where
  mem_X : β ∈ closure {t, w ^ (orderOf w / 2), z}
  not_mem : β ∉ zpowers t ⊔ (S ⊓ L)
  not_conj : ∀ g : X, g * t * g⁻¹ ≠ β
  exists_mem : ∃ v ∈ V ⊓ centralizer ({β} : Set X), v ∉ S ∧
    v ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
    (v * t * v⁻¹ = t * z ∨ v * t * v⁻¹ = t * β * z)
  lt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w < V ⊓ centralizer ({β} : Set X)
  isSylowOf : IsSylowOf 2 (V ⊓ centralizer ({β} : Set X)) (centralizer ({β} : Set X) ⊓
    normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
  fusion : ∀ g ∈ centralizer ({β} : Set X),
    g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} →
      ∃ v ∈ V ⊓ centralizer ({β} : Set X), v * t * v⁻¹ = g * t * g⁻¹
  inf_eq : V ⊓ centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X) =
    zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  relIndex_le : (V ⊓ centralizer ({β} : Set X)).relIndex V ≤ 2
  twoPart_le : twoPart (⊤ : Subgroup X) ≤ 4 * twoPart (centralizer ({β} : Set X))
  of_ne : (∃ g : X, g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} ∧
      ∀ v ∈ V ⊓ centralizer ({β} : Set X), v * t * v⁻¹ ≠ g * t * g⁻¹) →
    S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
      ∃ v ∈ V, v ^ 2 ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w

theorem card_le_twoPart [Finite X] {P K : Subgroup X} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    Nat.card P ≤ twoPart K := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge hP hPK
  calc Nat.card P ≤ Nat.card Q := Subgroup.card_le_of_le hPQ
    _ = twoPart K := hQ.card_eq

theorem twoPart_le_of_mem [Finite X] {Y E : Subgroup X} (hY : IsSylowOf 2 Y ⊤) (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hE8 : Nat.card E = 8) {β : X} (hβE : β ∈ E)
    (hβ1 : β ≠ 1) : twoPart (⊤ : Subgroup X) ≤ 4 * twoPart (centralizer ({β} : Set X)) := by
  classical
  have horb : {y : X | ∃ a ∈ Y, a * β * a⁻¹ = y} ⊆ (E : Set X) \ {1} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨hEn a ha β hβE, fun h1 => hβ1 ?_⟩
    have h1' : a * β * a⁻¹ = 1 := h1
    calc β = a⁻¹ * (a * β * a⁻¹) * a := by group
      _ = 1 := by rw [h1']; group
  have hE7 : ((E : Set X) \ {1}).ncard = 7 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem E), ← Nat.card_coe_set_eq]
    have : Nat.card ((E : Set X)) = Nat.card E := rfl
    omega
  have hle7 := (Set.ncard_le_ncard horb (Set.toFinite _)).trans hE7.le
  rw [ncard_conj_orbit Y (hEY hβE)] at hle7
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY.isPGroup
  have hdvd : (centralizer ({β} : Set X)).relIndex Y ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card (H := centralizer ({β} : Set X)) (K := Y)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hle4 : (centralizer ({β} : Set X)).relIndex Y ≤ 4 := by
    rw [he] at hle7 ⊢
    rcases e with _ | _ | _ | e
    · norm_num
    · norm_num
    · norm_num
    · exfalso
      have : 8 ≤ 2 ^ (e + 1 + 1 + 1) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (e + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have h1 := Subgroup.relIndex_mul_card (H := centralizer ({β} : Set X)) (K := Y)
  have h2 : Nat.card (centralizer ({β} : Set X) ⊓ Y : Subgroup X) ≤
      twoPart (centralizer ({β} : Set X)) :=
    card_le_twoPart (hY.isPGroup.to_le inf_le_right) inf_le_left
  have h3 : twoPart (⊤ : Subgroup X) = Nat.card Y := hY.card_eq.symm
  rw [h3, ← h1]
  calc (centralizer ({β} : Set X)).relIndex Y *
        Nat.card (centralizer ({β} : Set X) ⊓ Y : Subgroup X) ≤
      4 * Nat.card (centralizer ({β} : Set X) ⊓ Y : Subgroup X) := Nat.mul_le_mul_right _ hle4
    _ ≤ 4 * twoPart (centralizer ({β} : Set X)) := Nat.mul_le_mul_left _ h2

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem inf_centralizer_inf_t [Finite X] (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {β : X} (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z})
    (hβD : β ∉ zpowers t ⊔ (S ⊓ L)) :
    V ⊓ centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  obtain ⟨i, j, hβ⟩ := hσ.mem_X_not_tD hβX hβD
  have hSyl := hσ.isSylowOf_centralizer hKC i j
  rw [← hβ] at hSyl
  have hTβ : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({β} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hβX).2 y hy)
  exact hSyl.eq_of_le (le_inf (le_inf (hσ.T_le.trans hSV) hTβ) (hσ.T_le.trans hS.le))
    (fun y hy => Subgroup.mem_inf.mpr ⟨hy.2, hy.1.2⟩)
    (hV.isPGroup.to_le (inf_le_left.trans inf_le_left))

theorem isSylowOf_inf_centralizer [Finite X] (hKF : AutPSL2FusionInput)
    (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    {β : X} (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) :
    IsSylowOf 2 (V ⊓ centralizer ({β} : Set X)) (centralizer ({β} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) := by
  classical
  have hPK : V ⊓ centralizer ({β} : Set X) ≤ centralizer ({β} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    fun y hy => Subgroup.mem_inf.mpr ⟨hy.2, hV.le hy.1⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge (hV.isPGroup.to_le inf_le_left) hPK
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_ge hQ.isPGroup (hQ.le.trans inf_le_right)
  obtain ⟨k, hk, hkQ⟩ := hV.exists_mem_conj hQ'
  obtain ⟨P₀, hP₀⟩ := hV.exists_sylow_eq_subgroupOf
  obtain ⟨x, hxP, hx⟩ := exists_eq_of_isPGroup_range hσ.normalizerTAction
    (hσ.isPGroup_range hKF) P₀ ⟨k, hk⟩
  have hxV : (x : X) ∈ V := by
    have : x ∈ (P₀ : Subgroup _) := hxP
    rw [hP₀] at this
    exact this
  have hβk : k⁻¹ * β * k ∈ closure {t, w ^ (orderOf w / 2), z} := by
    have := (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X (inv_mem hk)) β).mp hβX
    rwa [inv_inv] at this
  have hkx : β = x * (k⁻¹ * β * k) * (x : X)⁻¹ := by
    have h1 := congrArg (fun φ : MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) =>
      ((φ ⟨_, hβk⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) : X)) hx
    simp only [normalizerTAction_apply] at h1
    calc β = k * (k⁻¹ * β * k) * k⁻¹ := by group
      _ = x * (k⁻¹ * β * k) * (x : X)⁻¹ := h1
  have hle : Q.map (MulAut.conj k⁻¹).toMonoidHom ≤
      (V ⊓ centralizer ({β} : Set X)).map (MulAut.conj (x : X)⁻¹).toMonoidHom := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨x * (k⁻¹ * q * k) * (x : X)⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · have hqV : k⁻¹ * q * k ∈ V := (hkQ q).mp (hQQ' hq)
      exact V.mul_mem (V.mul_mem hxV hqV) (V.inv_mem hxV)
    · rw [mem_centralizer_singleton_iff]
      have hqβ := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hQ.le hq)).1
      calc x * (k⁻¹ * q * k) * (x : X)⁻¹ * β =
          x * (k⁻¹ * q * k) * (x : X)⁻¹ * (x * (k⁻¹ * β * k) * (x : X)⁻¹) := by rw [← hkx]
        _ = x * (k⁻¹ * (q * β) * k) * (x : X)⁻¹ := by group
        _ = x * (k⁻¹ * (β * q) * k) * (x : X)⁻¹ := by rw [hqβ]
        _ = x * (k⁻¹ * β * k) * (x : X)⁻¹ * (x * (k⁻¹ * q * k) * (x : X)⁻¹) := by group
        _ = β * (x * (k⁻¹ * q * k) * (x : X)⁻¹) := by rw [← hkx]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hcard : Nat.card Q ≤ Nat.card (V ⊓ centralizer ({β} : Set X) : Subgroup X) := by
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective, Subgroup.card_map_of_injective
      (f := (MulAut.conj (x : X)⁻¹).toMonoidHom) (MulAut.conj (x : X)⁻¹).injective] at h1
  have heq : V ⊓ centralizer ({β} : Set X) = Q := Subgroup.eq_of_le_of_card_ge hPQ hcard
  rw [heq]
  exact hQ

theorem exists_conj_of_mem_centralizer [Finite X] (hKF : AutPSL2FusionInput)
    (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    {β : X} (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) {g : X}
    (hg : g ∈ centralizer ({β} : Set X))
    (hgX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z}) :
    ∃ v ∈ V ⊓ centralizer ({β} : Set X), v * t * v⁻¹ = g * t * g⁻¹ := by
  have hTβ : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({β} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hβX).2 y hy)
  exact hσ.exists_conj_W hKF hTβ (hσ.isSylowOf_inf_centralizer hKF hV hβX) hg hgX

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
