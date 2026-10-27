module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKill

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem exists_like_conj_of_transfer [Finite G] {t : G}
    (hG : ∀ K : Subgroup G, K.index = 2 → t ∈ K) (ht2 : t * t = 1) {TH T M : Subgroup G}
    (hTp : IsPGroup 2 T) (hTmax : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T)
    (hTHT : TH ≤ T) (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hM : M.relIndex T = 2) :
    ∃ u ∈ M, ∃ g : G, g * t * g⁻¹ = u ∧
      TH.map (MulAut.conj g).toMonoidHom = T ⊓ centralizer ({u} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 G := ⟨T, hTp, fun hQ hle => hTmax _ hQ hle⟩
  obtain ⟨g, hgM, hodd⟩ := CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T' hM
    (by rw [pow_two, ht2]) hG
  set u := g * t * g⁻¹ with hu
  refine ⟨u, hgM, ?_⟩
  have hTC : T ⊓ centralizer ({t} : Set G) = TH := inf_centralizer_eq hTp hTHT hTH hTHmax
  have hA : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V →
      T ⊓ centralizer ({u} : Set G) ≤ V → V = T ⊓ centralizer ({u} : Set G) := by
    intro V hV hVp hle
    have hmul := relIndex_mul_relIndex _ _ _ hle hV
    rw [inf_relIndex_right] at hmul
    have hd : (T ⊓ centralizer ({u} : Set G)).relIndex V ∣ Nat.card V := relIndex_dvd_card _ _
    obtain ⟨m, hm⟩ := hVp.exists_card_eq
    rw [hm] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have h1 : (T ⊓ centralizer ({u} : Set G)).relIndex V = 1 := by
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [← hmul, hj, pow_succ, mul_assoc] at hodd
        exact Nat.not_odd_iff_even.2 even_two (Nat.odd_mul.1 (Nat.odd_mul.1 hodd).2).1
    exact le_antisymm (relIndex_eq_one.1 h1) hle
  have hB : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V →
      TH.map (MulAut.conj g).toMonoidHom ≤ V → V = TH.map (MulAut.conj g).toMonoidHom := by
    intro V hV hVp hle
    set W := V.map (MulAut.conj g⁻¹).toMonoidHom
    have hW : W ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨v, hv, rfl⟩
      have hvu := mem_centralizer_singleton_iff.1 (hV hv)
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * v * g * t = g⁻¹ * (v * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * v) * g := by rw [← hu, hvu]
        _ = t * (g⁻¹ * v * g) := by group
    have hWp : IsPGroup 2 W := hVp.map _
    have hTHW : TH ≤ W := by
      intro x hx
      refine ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have hWeq := hTHmax W hW hWp hTHW
    ext y
    constructor
    · intro hy
      have : g⁻¹ * y * g ∈ TH := by
        rw [← hWeq]; exact ⟨y, hy, by simp⟩
      exact ⟨g⁻¹ * y * g, this, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · intro hy; exact hle hy
  have hBle : TH.map (MulAut.conj g).toMonoidHom ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt := mem_centralizer_singleton_iff.1 (hTH hx)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  obtain ⟨k, hkC, hk⟩ := exists_conj_of_max inf_le_right hBle (hTp.to_le inf_le_left)
    ((hTp.to_le hTHT).map _) hA hB
  have hmap : (T ⊓ centralizer ({t} : Set G)).map (MulAut.conj (k * g)).toMonoidHom =
      T ⊓ centralizer ({u} : Set G) := by
    rw [hTC, ← hk, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hku : k * g * t * (k * g)⁻¹ = u := by
    have hku' := mem_centralizer_singleton_iff.1 hkC
    calc k * g * t * (k * g)⁻¹ = k * u * k⁻¹ := by rw [hu]; group
      _ = u := by rw [hku']; group
  exact ⟨k * g, hku, by rw [← hmap, hTC]⟩

structure L2Data (t : G) (TH T₁ T₂ : Subgroup G) : Prop where
  B : ∀ u, Like T₁ t u → ∃ h ∈ T₂, h * t * h⁻¹ = u
  C : ∀ v ∈ T₂, v ∉ T₁ → v * v = 1 →
    Nat.card (T₂ ⊓ centralizer ({v} : Set G) : Subgroup G) < Nat.card TH
  D : ∀ u ∈ T₁, u * u = 1 →
    2 * Nat.card (T₁ ⊓ centralizer ({u} : Set G) : Subgroup G) = Nat.card TH →
      T₂ ⊓ centralizer ({u} : Set G) ≤ T₁ ∨
      ∀ K : Subgroup G, K ≤ TH → K.relIndex TH = 2 → t ∈ K →
        (nInv K, nOrd4 K) ≠ (nInv (T₁ ⊓ centralizer ({u} : Set G)),
          nOrd4 (T₁ ⊓ centralizer ({u} : Set G)))

section

variable [Finite G] {t : G} {TH T₁ T₂ : Subgroup G}

omit [Finite G] in
theorem card_map_conj (g : G) (H : Subgroup G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H := card_map _ _

theorem conj_of_map (hD : L2Data t TH T₁ T₂) (ht2 : t * t = 1)
    (hT₁p : IsPGroup 2 T₁) (hTHT₁ : TH ≤ T₁) (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hT₁₂ : T₁ ≤ T₂) (hidx : T₁.relIndex T₂ = 2) {g u : G} (hgu : g * t * g⁻¹ = u)
    (huT : u ∈ T₂) (hmap : TH.map (MulAut.conj g).toMonoidHom = T₂ ⊓ centralizer ({u} : Set G)) :
    ∃ h ∈ T₂, h * t * h⁻¹ = u := by
  have hu2 : u * u = 1 := by
    rw [← hgu, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2]; group
  have hcard : Nat.card (T₂ ⊓ centralizer ({u} : Set G) : Subgroup G) = Nat.card TH := by
    rw [← hmap, card_map_conj]
  have huT₁ : u ∈ T₁ := by
    by_contra h
    exact absurd (hD.C u huT h hu2) (by rw [hcard]; exact lt_irrefl _)
  have hTC : T₁ ⊓ centralizer ({t} : Set G) = TH := inf_centralizer_eq hT₁p hTHT₁ hTH hTHmax
  by_cases hle : T₂ ⊓ centralizer ({u} : Set G) ≤ T₁
  ·
    have heq : T₁ ⊓ centralizer ({u} : Set G) = TH.map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      exact le_antisymm (inf_le_inf_right _ hT₁₂) (le_inf hle inf_le_right)
    refine hD.B u ⟨huT₁, hu2, ?_, ?_, ?_⟩
    · rw [heq, hTC, card_map_conj]
    · rw [heq, hTC, nInv_map]
    · rw [heq, hTC, nOrd4_map]
  ·
    exfalso
    set C₂ := T₂ ⊓ centralizer ({u} : Set G)
    set C₁ := T₁ ⊓ centralizer ({u} : Set G)
    have hC₁ : C₁ = T₁ ⊓ C₂ := by
      simp only [C₁, C₂, ← inf_assoc, inf_of_le_left hT₁₂]
    have hC₁C₂ : C₁ ≤ C₂ := inf_le_inf_right _ hT₁₂
    have hidx₁ : C₁.relIndex C₂ = 2 := by
      have hle2 : T₁.relIndex C₂ ≤ 2 :=
        hidx ▸ relIndex_le_of_le_right inf_le_left (by rw [hidx]; norm_num)
      have h0 : T₁.relIndex C₂ ≠ 0 := by
        intro h0
        have := relIndex_mul_card (H := T₁) (K := C₂)
        rw [h0, zero_mul] at this
        exact Nat.card_pos.ne this
      have hne : T₁.relIndex C₂ ≠ 1 := fun h1 => hle (relIndex_eq_one.1 h1)
      rw [hC₁, inf_relIndex_right]
      omega
    have hcard₁ : 2 * Nat.card C₁ = Nat.card TH := by
      have := relIndex_mul_card (H := C₁) (K := C₂)
      rw [hidx₁, inf_of_le_left hC₁C₂, hcard] at this
      exact this
    rcases hD.D u huT₁ hu2 hcard₁ with h | hK
    · exact hle h
    ·
      set K := C₁.map (MulAut.conj g⁻¹).toMonoidHom
      have hKC : K.map (MulAut.conj g).toMonoidHom = C₁ := by
        rw [map_map]
        conv_rhs => rw [← map_id C₁]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      have hKTH : K ≤ TH := by
        rintro _ ⟨x, hx, rfl⟩
        have : x ∈ TH.map (MulAut.conj g).toMonoidHom := by rw [hmap]; exact hC₁C₂ hx
        obtain ⟨y, hy, rfl⟩ := this
        simpa [MulAut.conj_apply, mul_assoc] using hy
      have htK : t ∈ K := by
        refine ⟨u, ⟨huT₁, mem_centralizer_singleton_iff.2 rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ← hgu]
        group
      have hKidx : K.relIndex TH = 2 := by
        have h1 := relIndex_mul_card (H := K) (K := TH)
        have h2 : Nat.card K = Nat.card C₁ := card_map_conj _ _
        have hpos : 0 < Nat.card C₁ := Nat.card_pos
        rw [inf_of_le_left hKTH, h2, ← hcard₁] at h1
        exact Nat.eq_of_mul_eq_mul_right hpos h1
      apply hK K hKTH hKidx htK
      change (nInv K, nOrd4 K) = (nInv C₁, nOrd4 C₁)
      rw [← nInv_map (MulAut.conj g) K, ← nOrd4_map (MulAut.conj g) K, hKC]

theorem max_of_L2 (hD : L2Data t TH T₁ T₂) (ht2 : t * t = 1) (htT₁ : t ∈ T₁)
    (hT₁p : IsPGroup 2 T₁) (hT₂p : IsPGroup 2 T₂) (hTHT₁ : TH ≤ T₁)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hT₁₂ : T₁ ≤ T₂) (hidx : T₁.relIndex T₂ = 2) :
    ∀ P : Subgroup G, IsPGroup 2 P → T₂ ≤ P → P = T₂ := by
  intro P hP hTP
  by_contra hne
  obtain ⟨n, hnP, hnN, hnT⟩ := Stage1.exists_mem_normalizer_not_mem hP (lt_of_le_of_ne hTP (Ne.symm hne))
  have hTC₂ : T₂ ⊓ centralizer ({t} : Set G) = TH :=
    inf_centralizer_eq hT₂p (hTHT₁.trans hT₁₂) hTH hTHmax
  have hmap : TH.map (MulAut.conj n).toMonoidHom =
      T₂ ⊓ centralizer ({n * t * n⁻¹} : Set G) := by
    rw [← hTC₂, map_conj_inf_centralizer hnN]
  have huT : n * t * n⁻¹ ∈ T₂ := (mem_normalizer_iff.1 hnN t).1 (hT₁₂ htT₁)
  obtain ⟨h, hhT, hht⟩ := conj_of_map hD ht2 hT₁p hTHT₁ hTH hTHmax hT₁₂ hidx rfl huT hmap
  have hc : h⁻¹ * n ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : t = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ := by
      calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
        _ = h⁻¹ * (n * t * n⁻¹) * h := by rw [hht]
        _ = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ := by group
    calc h⁻¹ * n * t = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ * (h⁻¹ * n) := by group
      _ = t * (h⁻¹ * n) := by rw [← this]
  have hPC : P ⊓ centralizer ({t} : Set G) = TH :=
    hTHmax _ inf_le_right (hP.to_le inf_le_left) (le_inf ((hTHT₁.trans hT₁₂).trans hTP) hTH)
  have hmem : h⁻¹ * n ∈ TH := by
    rw [← hPC]
    exact ⟨P.mul_mem (P.inv_mem (hTP hhT)) hnP, hc⟩
  apply hnT
  have : n = h * (h⁻¹ * n) := by group
  rw [this]
  exact mul_mem hhT ((hTHT₁.trans hT₁₂) hmem)

theorem false_of_L2 (hG : ∀ K : Subgroup G, K.index = 2 → t ∈ K) (hD : L2Data t TH T₁ T₂)
    (ht2 : t * t = 1) (htT₁ : t ∈ T₁) (hT₁p : IsPGroup 2 T₁) (hT₂p : IsPGroup 2 T₂)
    (hTHT₁ : TH ≤ T₁) (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hT₁₂ : T₁ ≤ T₂) (hidx : T₁.relIndex T₂ = 2) {M : Subgroup G} (hMT : M ≤ T₂)
    (hM : M.relIndex T₂ = 2) (hMn : ∀ h ∈ T₂, ∀ x ∈ M, h * x * h⁻¹ ∈ M) (htM : t ∉ M) : False := by
  have hTmax := max_of_L2 hD ht2 htT₁ hT₁p hT₂p hTHT₁ hTH hTHmax hT₁₂ hidx
  obtain ⟨u, huM, g, hgu, hmap⟩ := exists_like_conj_of_transfer hG ht2 hT₂p hTmax
    (hTHT₁.trans hT₁₂) hTH hTHmax hM
  obtain ⟨h, hhT, rfl⟩ := conj_of_map hD ht2 hT₁p hTHT₁ hTH hTHmax hT₁₂ hidx hgu (hMT huM)
    hmap
  apply htM
  have := hMn h⁻¹ (inv_mem hhT) _ huM
  simpa [mul_assoc] using this

omit [Finite G] in
theorem like_conj_T₂ (htT₁ : t ∈ T₁) (ht2 : t * t = 1) (hT₂p : IsPGroup 2 T₂) (hTHT₁ : TH ≤ T₁)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hT₁₂ : T₁ ≤ T₂) {a b : G}
    (hab : ∀ u, Like T₁ t u → ∃ r ∈ ({a, b} : Set G), ∃ g ∈ T₁, g * r * g⁻¹ = u) {y : G}
    (hyN : y ∈ normalizer (T₁ : Set G)) (hyT₂ : y ∈ T₂) (hyT₁ : y ∉ T₁) :
    ∀ u, Like T₁ t u → ∃ h ∈ T₂, h * t * h⁻¹ = u := by
  have hTC : T₂ ⊓ centralizer ({t} : Set G) = TH :=
    inf_centralizer_eq hT₂p (hTHT₁.trans hT₁₂) hTH hTHmax
  have htl : Like T₁ t t := ⟨htT₁, ht2, rfl, rfl, rfl⟩
  have hyl : Like T₁ t (y * t * y⁻¹) := (like_conj hyN).2 htl
  obtain ⟨p, hp, g₁, hg₁, hpt⟩ := hab t htl
  obtain ⟨q, hq, g₂, hg₂, hqy⟩ := hab _ hyl
  have hnot : ∀ c ∈ T₁, c * t * c⁻¹ ≠ y * t * y⁻¹ := by
    intro c hc hct
    have hcy : c⁻¹ * y ∈ T₂ ⊓ centralizer ({t} : Set G) := by
      refine mem_inf.2 ⟨T₂.mul_mem (T₂.inv_mem (hT₁₂ hc)) hyT₂, mem_centralizer_singleton_iff.2 ?_⟩
      have : t = (c⁻¹ * y) * t * (c⁻¹ * y)⁻¹ := by
        calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
          _ = c⁻¹ * (y * t * y⁻¹) * c := by rw [hct]
          _ = (c⁻¹ * y) * t * (c⁻¹ * y)⁻¹ := by group
      calc c⁻¹ * y * t = (c⁻¹ * y) * t * (c⁻¹ * y)⁻¹ * (c⁻¹ * y) := by group
        _ = t * (c⁻¹ * y) := by rw [← this]
    rw [hTC] at hcy
    apply hyT₁
    have : y = c * (c⁻¹ * y) := by group
    rw [this]
    exact mul_mem hc (hTHT₁ hcy)
  have hpT : ∃ h ∈ T₂, h * t * h⁻¹ = p :=
    ⟨g₁⁻¹, inv_mem (hT₁₂ hg₁), by rw [← hpt]; group⟩
  have hqT : ∃ h ∈ T₂, h * t * h⁻¹ = q :=
    ⟨g₂⁻¹ * y, mul_mem (inv_mem (hT₁₂ hg₂)) hyT₂, by
      calc g₂⁻¹ * y * t * (g₂⁻¹ * y)⁻¹ = g₂⁻¹ * (y * t * y⁻¹) * g₂ := by group
        _ = g₂⁻¹ * (g₂ * q * g₂⁻¹) * g₂ := by rw [hqy]
        _ = q := by group⟩
  have hpq : p ≠ q := by
    rintro rfl
    apply hnot (g₂ * g₁⁻¹) (mul_mem hg₂ (inv_mem hg₁))
    calc g₂ * g₁⁻¹ * t * (g₂ * g₁⁻¹)⁻¹ = g₂ * (g₁⁻¹ * t * g₁) * g₂⁻¹ := by group
      _ = g₂ * p * g₂⁻¹ := by rw [← hpt]; group
      _ = y * t * y⁻¹ := hqy
  have hall : ∀ r ∈ ({a, b} : Set G), ∃ h ∈ T₂, h * t * h⁻¹ = r := by
    intro r hr
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
      first | exact hpT | exact hqT | exact absurd rfl hpq
  intro u hu
  obtain ⟨r, hr, g, hg, hgr⟩ := hab u hu
  obtain ⟨h, hh, hht⟩ := hall r hr
  exact ⟨g * h, mul_mem (hT₁₂ hg) hh, by rw [← hgr, ← hht]; group⟩

end

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
