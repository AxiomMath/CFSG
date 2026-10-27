module

public import CFSG.CGT.PushingUpLit.A78G0.Cliques
public import CFSG.CGT.PushingUpLit.A78S4.Cross

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.ABGLocalTools

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem exists_conj_L {x : G} (hx : x ∈ V) :
    ∃ g ∈ L₁, g⁻¹ * x * g ∈ Z ∨ g⁻¹ * x * g ∈ Z₂ ∨ UType V W Z Z₂ (g⁻¹ * x * g) := by
  by_cases hxZ : x ∈ Z
  · exact ⟨1, L₁.one_mem, Or.inl (by simpa using hxZ)⟩
  obtain ⟨D⟩ := h.pair.side₁.nat
  obtain ⟨fr⟩ := h.pair.side₁.exists_frame D
  obtain ⟨l, hl, hlx⟩ := D.exists_conj hx hxZ fr.hn₀.1 fr.hn₀Z
  have hlxV : l * x * l⁻¹ ∈ V := D.norm l hl x hx
  have hlxN : l * x * l⁻¹ ∈ V ⊓ W := by
    have h1 := (D.κ_eq_iff hlxV fr.hn₀.1).1 hlx
    have e1 : l * x * l⁻¹ = (l * x * l⁻¹ * fr.n₀⁻¹) * fr.n₀ := by group
    rw [e1]
    exact mul_mem (h.pair.side₁.Z_le_N h1) fr.hn₀
  have hlxZ : l * x * l⁻¹ ∉ Z := fun h1 => hxZ (by
    have : x = l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ := by group
    rw [this]
    exact conj_mem_of_mem_normalizer' (D.le_normalizer_K (inv_mem hl)) h1)
  obtain ⟨z, hz, z₂, hz₂, hdec⟩ := h.pair.exists_decomp h.hZ hlxN
  have hz₂1 : z₂ ≠ 1 := fun h1 => hlxZ (by rw [← hdec, h1, mul_one]; exact hz)
  refine ⟨l⁻¹, inv_mem hl, ?_⟩
  rw [inv_inv]
  by_cases hz1 : z = 1
  · exact Or.inr (Or.inl (by rw [← hdec, hz1, one_mul]; exact hz₂))
  · exact Or.inr (Or.inr (by rw [← hdec]; exact h.pair.utype_of_decomp h.hZ hz hz₂ hz1 hz₂1))

theorem not_conj_of_mem_V {u z : G} (huV : u ∈ V) (huZ : u ∉ Z) (hz : z ∈ Z) (c : G) :
    c * z * c⁻¹ ≠ u := by
  intro hc
  have hu1 : u ≠ 1 := fun h1 => huZ (by rw [h1]; exact Z.one_mem)
  have hmem : u ∈ cs Z c := by
    rw [← hc]
    exact conj_mem_cs c hz
  have hcs : cs Z c = Z := h.kl hmem huV hu1
  rw [hcs] at hmem
  exact huZ hmem

theorem cent_le_normalizer_J_of_le {u : G} (hu : u ∈ V ⊓ W) (huZ : u ∉ Z)
    (hC : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
  obtain ⟨D⟩ := h.pair.side₁.nat
  have hLC := h.pair.side₁.cent_L D hu huZ
  refine le_normalizer_of_conj' fun c hc j hj => ?_
  have hcL : c ∈ Subgroup.normalizer (L₁ : Set G) := h.M_le_normalizer_L (hC hc)
  have h1 : c * j * c⁻¹ ∈ L₁ := conj_mem_of_mem_normalizer' hcL (h.J_le_L hj)
  have hj' : j ∈ L₁ ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [hLC]
    exact hj
  have h2 : c * j * c⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
    mul_mem (mul_mem hc hj'.2) (inv_mem hc)
  have h3 : c * j * c⁻¹ ∈ L₁ ⊓ Subgroup.centralizer ({u} : Set G) := ⟨h1, h2⟩
  rw [hLC] at h3
  exact h3

theorem sup_N_cs_eq_W {g : G} (hg : cs Z g ≠ Z) (hgW : cs Z g ≤ W) :
    (V ⊓ W) ⊔ cs Z g = W := by
  have h1 := h.pair.symm.sup_eq_of_inf_eq_bot h.Z₂_ne_bot hgW (by rw [card_cs, h.card_Z]) (by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxV : x ∈ cs Z g ⊓ V := ⟨hx.2, hx.1.2⟩
    rw [h.cs_inf_V hg] at hxV
    exact hxV)
  rwa [inf_comm] at h1

theorem cent_le_normalizer_J {u : G} (hu : u ∈ V ⊓ W) (huZ : u ∉ Z) (huZ₂ : u ∉ Z₂) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  set Q := CFSG.Open.pCoreOf 2 C with hQdef
  have hu1 : u ≠ 1 := fun h1 => huZ (by rw [h1]; exact Z.one_mem)
  have huu : u * u = 1 := h.jst.sq_V u hu.1
  have hcomm : ∀ {n j : G}, n ∈ V ⊓ W → j ∈ V ⊔ W → n * j = j * n := fun {n j} hn hj =>
    (h.jst.commute_of_mem_inf hn hj).eq
  have hJC : V ⊔ W ≤ C := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm hu hj).symm
  have hJsyl : IsSylowOf 2 (V ⊔ W) C := h.sylow.of_le hJC le_top
  have hQJ : Q ≤ V ⊔ W := pCoreOf_le_of_isSylowOf hJsyl
  have hNQ : V ⊓ W ≤ Q := by
    intro n hn
    have hnC : n ∈ C := Subgroup.mem_centralizer_singleton_iff.2 (h.pair.commute_N hn hu)
    have hnQ : n ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun q hq => (hcomm hn (hQJ hq)).symm
    exact cent_le_pCoreOf h.charTwo huu hu1 ⟨hnC, hnQ⟩
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hQC : ∀ c ∈ C, ∀ B ≤ Q, cs B c ≤ Q := by
    intro c hc B hB x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact conj_mem_of_mem_normalizer' (hCQ hc) (hB hb)
  by_cases hB : ∃ B ∈ zClass Z, B ≠ Z ∧ B ≤ Q
  swap
  ·
    push Not at hB
    refine h.cent_le_normalizer_J_of_le hu huZ fun c hc => ?_
    have h1 : cs Z c ≤ Q := hQC c hc Z (h.Z_le_N.trans hNQ)
    have h2 : cs Z c = Z := by
      by_contra hne
      exact hB _ (cs_mem_zClass (self_mem_zClass Z) c) hne h1
    rw [← h.normalizer_Z_eq]
    exact mem_normalizer_of_cs_eq h2
  by_cases hB' : ∃ B ∈ zClass Z₂, B ≠ Z₂ ∧ B ≤ Q
  swap
  ·
    push Not at hB'
    have hu' : u ∈ W ⊓ V := by rwa [inf_comm]
    have := h.symm.cent_le_normalizer_J_of_le hu' huZ₂ fun c hc => by
      have h1 : cs Z₂ c ≤ Q := hQC c hc Z₂ (h.Z₂_le_N.trans hNQ)
      have h2 : cs Z₂ c = Z₂ := by
        by_contra hne
        exact hB' _ (cs_mem_zClass (self_mem_zClass Z₂) c) hne h1
      rw [← h.symm.normalizer_Z_eq]
      exact mem_normalizer_of_cs_eq h2
    rwa [sup_comm] at this
  obtain ⟨B, hBΔ, hBZ, hBQ⟩ := hB
  obtain ⟨B', hB'Δ, hB'Z, hB'Q⟩ := hB'
  obtain ⟨g, rfl⟩ := hBΔ
  obtain ⟨g', rfl⟩ := hB'Δ
  have hBW : cs Z g ≤ W := (h.cs_le_J (hBQ.trans hQJ)).resolve_left hBZ
  have hB'V : cs Z₂ g' ≤ V :=
    (h.symm.cs_le_J ((hB'Q.trans hQJ).trans (sup_comm V W).le)).resolve_left hB'Z
  have hWQ : W ≤ Q := (h.sup_N_cs_eq_W hBZ hBW).symm.le.trans (sup_le hNQ hBQ)
  have hVQ : V ≤ Q :=
    (h.symm.sup_N_cs_eq_W hB'Z hB'V).symm.le.trans
      (sup_le (by rw [inf_comm]; exact hNQ) hB'Q)
  have hQeq : Q = V ⊔ W := le_antisymm hQJ (sup_le hVQ hWQ)
  rw [← hQeq]
  exact hCQ

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
