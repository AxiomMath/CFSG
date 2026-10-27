module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Phi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2Seven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Used

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

section Generic

variable {G : Type} [Group G]

theorem exists_conjAut {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    ∃ α : MulAut ↥K, ∀ k : ↥K, ((α k : ↥K) : G) = g⁻¹ * (k : G) * g := by
  refine ⟨K.normalizerMonoidHom ⟨g⁻¹, (normalizer (K : Set G)).inv_mem hg⟩, fun k => ?_⟩
  show g⁻¹ * (k : G) * g⁻¹⁻¹ = g⁻¹ * (k : G) * g
  rw [inv_inv]

end Generic

section Elements

variable {G : Type} [Group G] [Finite G]

theorem IsA4Block.elements {L U : Subgroup G} (h : IsA4Block L U) {c z : G}
    (hcN : c ∈ normalizer (U : Set G)) (hc3 : c ^ 3 = 1)
    (hcfp : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u) (hzU : z ∈ U) (hz1 : z ≠ 1) :
    ∀ u ∈ U, u = 1 ∨ u = z ∨ u = c * z * c⁻¹ ∨ u = c * (c * z * c⁻¹) * c⁻¹ := by
  intro u hu
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · obtain ⟨n, hn⟩ := klein_conj_transitive h.card_U hc3 hcN hcfp hzU hu hz1 hu1
    have hn' : c ^ n = c ^ (n % 3) := pow_eq_pow_mod n hc3
    have e1 : c * c = c⁻¹ := eq_inv_of_mul_eq_one_left ((pow_three' c).symm.trans hc3)
    have e2 : c⁻¹ * c⁻¹ = c := by rw [← mul_inv_rev, e1, inv_inv]
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rw [hn'] at hn
    rcases hcases with h0 | h1 | h2
    · rw [h0] at hn
      simp at hn
      exact Or.inr (Or.inl hn)
    · rw [h1] at hn
      right; right; right
      rw [hn]
      calc (c ^ 1)⁻¹ * z * c ^ 1 = c⁻¹ * z * c := by simp
        _ = (c * c) * z * (c⁻¹ * c⁻¹) := by rw [e1, e2]
        _ = c * (c * z * c⁻¹) * c⁻¹ := by group
    · rw [h2] at hn
      right; right; left
      rw [hn]
      calc (c ^ 2)⁻¹ * z * c ^ 2 = (c * c)⁻¹ * z * (c * c) := by rw [pow_two]
        _ = c * z * c⁻¹ := by rw [e1, inv_inv]

end Elements

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G} {K : Subgroup G}

theorem A3A3K.exists_alpha (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) :
    ∃ u ∈ blockU2 L s, u ∉ Subgroup.centralizer (K : Set G) ∧ u ∈ centralizerElem z₂ ∧
      ∃ α : MulAut ↥K, (∀ k : ↥K, ((α k : ↥K) : G) = u⁻¹ * (k : G) * u) ∧
        (∀ k, α (α k) = k) ∧ (∃ k, α k ≠ k) ∧
        ∀ (l : G) (hl : l ∈ L), α ⟨l, hK.L_le_K hl⟩ = ⟨l, hK.L_le_K hl⟩ := by
  have hAs := hK.isA4s
  have hne := h34 G T M H S L s x z₁ z₂ K hK
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ blockU2 L s, u ∉ Subgroup.centralizer (K : Set G) := by
    by_contra hcon
    apply hne
    intro u hu
    by_contra hu'
    exact hcon ⟨u, hu, hu'⟩
  have hu2 : u * u = 1 := by
    have := hAs.sq_U u huU
    rwa [pow_two] at this
  have huG : u ∈ centralizerElem z₂ :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAs.comm_U u huU z₂ hK.z₂_mem.1)
  obtain ⟨α, hα⟩ := exists_conjAut (hK.K_norm huG)
  refine ⟨u, huU, hu, huG, α, hα, ?_, ?_, ?_⟩
  · intro k
    apply Subtype.ext
    rw [hα, hα]
    calc u⁻¹ * (u⁻¹ * (k : G) * u) * u = (u * u)⁻¹ * (k : G) * (u * u) := by group
      _ = k := by rw [hu2]; group
  · by_contra hcon
    apply hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hall : ∀ k' : ↥K, α k' = k' := fun k' => by
      by_contra h'
      exact hcon ⟨k', h'⟩
    have h1 := congrArg Subtype.val (hall ⟨k, hk⟩)
    rw [hα] at h1
    calc k * u = u * (u⁻¹ * k * u) := by group
      _ = u * k := by rw [show u⁻¹ * k * u = k from h1]
  · intro l hl
    apply Subtype.ext
    rw [hα]
    have hcomm := hK.comm_elem l hl u (hAs.le huU)
    calc u⁻¹ * l * u = u⁻¹ * (l * u) := by group
      _ = u⁻¹ * (u * l) := by rw [hcomm]
      _ = l := by group

theorem A3A3K.nonempty_alt6
    (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) :
    Nonempty (↥K ≃* alternatingGroup (Fin 6)) := by
  rcases hK.K_iso with h | ⟨⟨e₁⟩⟩
  · exact h
  · exfalso
    obtain ⟨u, huU, hu, huG, α, hα, hα2, hα1, hαL⟩ := hK.exists_alpha h34
    obtain ⟨k, hk⟩ := hα1
    exact hk (psl27_aut_eq_one e₁ hK.isA4 hK.L_le_K α hαL k)

theorem lemma2_4_35_used_of_34
    (h34 : Lemma2_4_34_used) : Lemma2_4_35_used := by
  intro G _ _ T M H S L s x z₁ z₂ K hK
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  obtain ⟨u, huU, hu, huG, α, hα, hα2, hα1, hαL⟩ := hK.exists_alpha h34
  have hcard : Nat.card ↥(L.subgroupOf K) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.L_le_K).toEquiv]
    exact hK.isA4.card_L
  obtain ⟨e, he⟩ := exists_iso_swap e₀ α hα2 hα1 (L.subgroupOf K) hcard
    (fun l hl => hαL (l : G) (Subgroup.mem_subgroupOf.mp hl))
  refine ⟨e, u, huU, ?_, tau, tau_isSwap, ?_⟩
  · intro hz
    apply hu
    have hz₂K : z₂ ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.mp (hK.K_comp.1 hk)
    exact (Subgroup.zpowers_le.mpr hz₂K) hz
  · intro k k' hk'
    have : k' = α k := Subtype.ext (hk'.trans (hα k).symm)
    rw [this]
    exact he k

end Config

section NotS6

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G} {K : Subgroup G}

theorem A3A3K.exists_aut_not_mem_s6 (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hK : A3A3K T M H S L s x z₁ z₂ K) (φ : ↥K ≃* ↥A6Models.psl29)
    {u : G} (huU : u ∈ blockU2 L s) (αu : MulAut ↥K)
    (hαu : ∀ k : ↥K, ((αu k : ↥K) : G) = u⁻¹ * (k : G) * u)
    (hφ : ∀ k : ↥K, ((φ (αu k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹) :
    ∃ αx : MulAut ↥K, (∀ k : ↥K, ((αx k : ↥K) : G) = x⁻¹ * (k : G) * x) ∧
      ∃ b : P10, b ∈ A6Models.autA6 ∧ b ∉ s6 ∧ ∀ k : ↥K,
        ((φ (αx k) : ↥A6Models.psl29) : P10) = b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹ := by
  have hAs := hK.isA4s
  have hA := hK.isA4
  have hxG : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  obtain ⟨αx, hαx⟩ := exists_conjAut (hK.K_norm hxG)
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ αx
  refine ⟨αx, hαx, b, hbA, ?_, hb⟩
  intro hbs
  obtain ⟨c, hcL, hc, hcN, hcfp, -⟩ := hA.exists_c
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcK : c ∈ K := hK.L_le_K hcL
  have hz₁U : z₁ ∈ blockU L := hK.z₁_mem.1
  have hUK : blockU L ≤ K := hA.le.trans hK.L_le_K
  have hz₁K : z₁ ∈ K := hUK hz₁U
  let ψ : ↥K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hψmem : ∀ k : ↥K, ψ k ∈ A6Models.psl29 := fun k => (φ k).2
  let cK : ↥K := ⟨c, hcK⟩
  let zK : ↥K := ⟨z₁, hz₁K⟩
  let w₂ : ↥K := cK * zK * cK⁻¹
  let w₃ : ↥K := cK * w₂ * cK⁻¹
  have hτ : ∀ k : ↥K, αu k = k → ψ k * A6Models.tFrob = A6Models.tFrob * ψ k := by
    intro k hk
    have h : ψ (αu k) = A6Models.tFrob * ψ k * A6Models.tFrob⁻¹ := hφ k
    rw [hk] at h
    calc ψ k * A6Models.tFrob = (A6Models.tFrob * ψ k * A6Models.tFrob⁻¹) * A6Models.tFrob := by
          rw [← h]
      _ = A6Models.tFrob * ψ k := by group
  have hαuL : ∀ (l : G) (hl : l ∈ L), αu ⟨l, hK.L_le_K hl⟩ = ⟨l, hK.L_le_K hl⟩ := by
    intro l hl
    apply Subtype.ext
    rw [hαu]
    have hcomm := hK.comm_elem l hl u (hAs.le huU)
    calc u⁻¹ * l * u = u⁻¹ * (l * u) := by group
      _ = u⁻¹ * (u * l) := by rw [hcomm]
      _ = l := by group
  have hcross := (hK.toA3A3x.cross_comm hD h27_1).2
  have hαuX : ∀ (w : G) (hw : w ∈ blockU L) (hwK : w ∈ K), αu (αx ⟨w, hwK⟩) = αx ⟨w, hwK⟩ := by
    intro w hw hwK
    apply Subtype.ext
    rw [hαu, hαx]
    have hmem : x⁻¹ * w * x ∈ conjR (blockU L) x := by
      rw [mem_conjR]
      have : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
      rw [this]
      exact hw
    have hcomm := hcross u huU (x⁻¹ * w * x) hmem
    calc u⁻¹ * (x⁻¹ * w * x) * u = u⁻¹ * ((x⁻¹ * w * x) * u) := by group
      _ = u⁻¹ * (u * (x⁻¹ * w * x)) := by rw [← hcomm]
      _ = x⁻¹ * w * x := by group
  have hUc : ∀ v ∈ blockU L, c * v * c⁻¹ ∈ blockU L := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hcN v).mp hv
  have hcK3 : cK ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcK1 : cK ≠ 1 := by
    intro h
    have h1 : c = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hc
    omega
  have hzK2 : zK * zK = 1 := Subtype.ext (by simpa [pow_two] using hA.sq_U z₁ hz₁U)
  have hzK1 : zK ≠ 1 := fun h => hK.z₁_ne (congrArg Subtype.val h)
  have hczK : cK * zK * cK⁻¹ ≠ zK := fun h => hcfp z₁ hz₁U hK.z₁_ne (congrArg Subtype.val h)
  have hcommK : (cK * zK * cK⁻¹) * zK = zK * (cK * zK * cK⁻¹) :=
    Subtype.ext (hA.comm_U (c * z₁ * c⁻¹) (hUc z₁ hz₁U) z₁ hz₁U)
  have hP1 : ψ cK ^ 3 = 1 := by rw [← map_pow, hcK3, map_one]
  have hP2 : ψ cK ≠ 1 := fun h => hcK1 (hψinj (h.trans (map_one ψ).symm))
  have hP3 : ψ zK * ψ zK = 1 := by rw [← map_mul, hzK2, map_one]
  have hP4 : ψ zK ≠ 1 := fun h => hzK1 (hψinj (h.trans (map_one ψ).symm))
  have hψw₂ : ψ w₂ = ψ cK * ψ zK * (ψ cK)⁻¹ := by simp [w₂]
  have hψw₃ : ψ w₃ = ψ cK * (ψ cK * ψ zK * (ψ cK)⁻¹) * (ψ cK)⁻¹ := by simp [w₃, w₂]
  have hP5 : ψ cK * ψ zK * (ψ cK)⁻¹ ≠ ψ zK := by
    rw [← hψw₂]
    exact fun h => hczK (hψinj h)
  have hP6 : (ψ cK * ψ zK * (ψ cK)⁻¹) * ψ zK = ψ zK * (ψ cK * ψ zK * (ψ cK)⁻¹) := by
    have := congrArg ψ hcommK
    simpa [map_mul, map_inv] using this
  have hy : ∀ k : ↥K, b * ψ k = ψ (αx k) * b := by
    intro k
    have h : ψ (αx k) = b * ψ k * b⁻¹ := hb k
    calc b * ψ k = (b * ψ k * b⁻¹) * b := by group
      _ = ψ (αx k) * b := by rw [← h]
  have hwK₂ : c * z₁ * c⁻¹ ∈ K := (w₂).2
  have hwK₃ : c * (c * z₁ * c⁻¹) * c⁻¹ ∈ K := (w₃).2
  have hτ₁ := hτ (αx zK) (hαuX z₁ hz₁U hz₁K)
  have hτ₂ := hτ (αx w₂) (hαuX (c * z₁ * c⁻¹) (hUc z₁ hz₁U) hwK₂)
  have hτ₃ := hτ (αx w₃) (hαuX (c * (c * z₁ * c⁻¹) * c⁻¹) (hUc _ (hUc z₁ hz₁U)) hwK₃)
  obtain ⟨h₁, h₂, h₃⟩ := klein_stable_P10 (hψmem cK) (hψmem zK) hbs
    (hτ cK (hαuL c hcL)) (hτ zK (hαuL z₁ (hA.le hz₁U))) hP1 hP2 hP3 hP4 hP5 hP6
    (hψmem _) (hψmem _) (hψmem _) (hy zK) (by rw [← hψw₂]; exact hy w₂)
    (by rw [← hψw₃]; exact hy w₃) hτ₁ hτ₂ hτ₃
  have conv : ∀ k : ↥K, (ψ k = ψ zK ∨ ψ k = ψ cK * ψ zK * (ψ cK)⁻¹ ∨
      ψ k = ψ cK * (ψ cK * ψ zK * (ψ cK)⁻¹) * (ψ cK)⁻¹) → (k = zK ∨ k = w₂ ∨ k = w₃) := by
    intro k hk
    rcases hk with h | h | h
    · exact Or.inl (hψinj h)
    · exact Or.inr (Or.inl (hψinj (h.trans hψw₂.symm)))
    · exact Or.inr (Or.inr (hψinj (h.trans hψw₃.symm)))
  have hmemU : ∀ k : ↥K, (k = zK ∨ k = w₂ ∨ k = w₃) → (k : G) ∈ blockU L := by
    intro k hk
    rcases hk with rfl | rfl | rfl
    · exact hz₁U
    · exact hUc z₁ hz₁U
    · exact hUc _ (hUc z₁ hz₁U)
  have hconj : ∀ y ∈ conjR (blockU L) x, y ∈ blockU L := by
    intro y hy
    have hw : x * y * x⁻¹ ∈ blockU L := mem_conjR.mp hy
    have hwK : x * y * x⁻¹ ∈ K := hUK hw
    have hyeq : y = ((αx ⟨x * y * x⁻¹, hwK⟩ : ↥K) : G) := by
      rw [hαx]
      group
    rw [hyeq]
    rcases hA.elements hcN hc3 hcfp hz₁U hK.z₁_ne (x * y * x⁻¹) hw with h1 | h1 | h1 | h1
    · have h0 : (⟨x * y * x⁻¹, hwK⟩ : ↥K) = 1 := Subtype.ext h1
      rw [h0, map_one]
      exact (blockU L).one_mem
    · have h0 : (⟨x * y * x⁻¹, hwK⟩ : ↥K) = zK := Subtype.ext h1
      rw [h0]
      exact hmemU _ (conv _ h₁)
    · have h0 : (⟨x * y * x⁻¹, hwK⟩ : ↥K) = w₂ := Subtype.ext h1
      rw [h0]
      exact hmemU _ (conv _ h₂)
    · have h0 : (⟨x * y * x⁻¹, hwK⟩ : ↥K) = w₃ := Subtype.ext h1
      rw [h0]
      exact hmemU _ (conv _ h₃)
  apply hK.x_good
  intro y hy
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => hA.comm_U v hv y (hconj y hy)

theorem lemma2_4_36_surj_of_34
    (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (h34 : Lemma2_4_34_used) : Lemma2_4_36_surj := by
  intro G _ _ T M H S L s x z₁ z₂ K hK α
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  obtain ⟨u, huU, hu, huG, αu, hαu, hαu2, hαu1, hαuL⟩ := hK.exists_alpha h34
  have hcard : Nat.card ↥(L.subgroupOf K) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.L_le_K).toEquiv]
    exact hK.isA4.card_L
  obtain ⟨φ, hφ⟩ := exists_swap_model e₀ αu hαu2 hαu1 (L.subgroupOf K) hcard
    (fun l hl => hαuL (l : G) (Subgroup.mem_subgroupOf.mp hl))
  obtain ⟨αx, hαx, b, hbA, hbs, hb⟩ := hK.exists_aut_not_mem_s6 hD h27_1 φ huU αu hαu hφ
  have hxG : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  let Hk : Subgroup (MulAut ↥K) :=
    { carrier := {γ | ∃ g ∈ centralizerElem z₂, ∀ k : ↥K,
        ((γ k : ↥K) : G) = g⁻¹ * (k : G) * g}
      mul_mem' := by
        rintro γ₁ γ₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
        refine ⟨g₂ * g₁, (centralizerElem z₂).mul_mem hg₂ hg₁, fun k => ?_⟩
        show ((γ₁ (γ₂ k) : ↥K) : G) = _
        rw [h₁, h₂]
        group
      one_mem' := ⟨1, (centralizerElem z₂).one_mem, fun k => by simp⟩
      inv_mem' := by
        rintro γ ⟨g, hg, h⟩
        refine ⟨g⁻¹, (centralizerElem z₂).inv_mem hg, fun k => ?_⟩
        have h' := h (γ⁻¹ k)
        have e : γ (γ⁻¹ k) = k := γ.apply_symm_apply k
        rw [e] at h'
        calc ((γ⁻¹ k : ↥K) : G) = g * (g⁻¹ * ((γ⁻¹ k : ↥K) : G) * g) * g⁻¹ := by group
          _ = g * (k : G) * g⁻¹ := by rw [← h']
          _ = g⁻¹⁻¹ * (k : G) * g⁻¹ := by rw [inv_inv] }
  have h1 : ∀ k₀ : ↥K, MulAut.conj k₀ ∈ Hk := by
    intro k₀
    refine ⟨(k₀ : G)⁻¹, hK.K_comp.1 (K.inv_mem k₀.2), fun k => ?_⟩
    simp [MulAut.conj_apply]
  have h2 : ∃ γ ∈ Hk, ∀ k : ↥K, ((φ (γ k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹ :=
    ⟨αu, ⟨u, huG, hαu⟩, hφ⟩
  have h3 : ∃ γ ∈ Hk, ∃ b : P10, b ∈ A6Models.autA6 ∧ b ∉ s6 ∧ ∀ k : ↥K,
      ((φ (γ k) : ↥A6Models.psl29) : P10) = b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹ :=
    ⟨αx, ⟨x, hxG, hαx⟩, b, hbA, hbs, hb⟩
  have htop := mulAut_eq_top_of_model φ Hk h1 h2 h3
  have hα : α ∈ Hk := htop ▸ Subgroup.mem_top α
  exact hα

end NotS6

end CFSG.QuasithinUnique.DoubleA3
