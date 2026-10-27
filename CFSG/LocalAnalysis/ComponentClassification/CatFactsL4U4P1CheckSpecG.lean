module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem map_oddPart_of_injective {S S' : Type} [Group S] [Group S'] (f : S →* S')
    (hf : Function.Injective f) (H : Subgroup S) :
    (Q81.oddPart H).map f = Q81.oddPart (H.map f) := by
  rw [Q81.oddPart, Q81.oddPart, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [orderOf_injective f hf]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by rwa [orderOf_injective f hf] at hodd⟩, rfl⟩

theorem map_centralizer_eq {P : Type} [Group P] {n : ℕ} (π : P →* Equiv.Perm (Fin n))
    (hπ : Function.Injective π) {A₀ : Subgroup (Equiv.Perm (Fin n))} (hr : π.range = A₀)
    (s : P) : (centralizer ({s} : Set P)).map π = A₀ ⊓ centralizer ({π s} : Set _) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨hr ▸ ⟨x, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · intro hy
    obtain ⟨hyA, hyc⟩ := mem_inf.mp hy
    rw [← hr] at hyA
    obtain ⟨x, rfl⟩ := hyA
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hyc
    exact hπ hyc

theorem card_oddPart_conj {n : ℕ} (A₀ : Subgroup (Equiv.Perm (Fin n))) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ A₀) (t : Equiv.Perm (Fin n)) :
    Nat.card ↥(Q81.oddPart (A₀ ⊓ centralizer ({g * t * g⁻¹} : Set _))) =
      Nat.card ↥(Q81.oddPart (A₀ ⊓ centralizer ({t} : Set _))) := by
  rw [inf_centralizer_conj A₀ hg t, ← map_oddPart_of_injective _ (MulAut.conj g).injective,
    card_map_of_injective (MulAut.conj g).injective]

theorem map_conj_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  have hcK := mem_normalizer_iff.mp (hHK hc)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨c * y * c⁻¹, (hcK y).mp hy, by group⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · have h1 := (hcK (c⁻¹ * y * c)).mpr (by rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group])
      exact h1
    · calc g * (c⁻¹ * y * c) * g⁻¹ = (g * c * g⁻¹)⁻¹ * (g * y * g⁻¹) * (g * c * g⁻¹) := by group
        _ = _ := by rw [hyx]; group

variable {n : ℕ} {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem extraOK_spec (hD : GroupData n A₀ pg gg sift) {u : Table} (h : extraOK n pg sift u = true) :
    Rep n u (tp n u) ∧ (∀ p ∈ A₀, tp n u * p * (tp n u)⁻¹ ∈ A₀) ∧ tp n u * tp n u ∉ A₀ := by
  simp only [extraOK, Bool.and_eq_true, Bool.not_eq_true', Array.all_eq_true] at h
  obtain ⟨⟨⟨hp, hi⟩, hsq⟩, hgen⟩ := h
  have hU := rep_tp hp
  have hUi := rep_invT hU hi
  refine ⟨hU, ?_, fun hm => ?_⟩
  · have hle : A₀.map (MulAut.conj (tp n u)).toMonoidHom ≤ A₀ := by
      rw [hD.gen, MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      have hl' : l < pg.size := hl
      have h1 := hgen l hl'
      rw [← getElem!_pos pg l hl'] at h1
      have h2 := rep_conjT hU hUi (hD.rep l hl')
      have h3 := (hD.sift _ _ h2).1 h1
      rw [hD.gen] at h3
      exact h3
    intro p hp'
    exact hle ⟨p, hp', rfl⟩
  · rw [← (hD.sift _ _ (Rep.compT hU hU))] at hm
    rw [hm] at hsq
    exact Bool.noConfusion hsq

theorem mem_A₀_or_run_of_involution (hD : GroupData n A₀ pg gg sift) {runs : List Run}
    {extra : List Table} (hextra : ∀ u ∈ extra, extraOK n pg sift u = true)
    {τ : Equiv.Perm (Fin n)} (hτ2 : orderOf τ = 2)
    (hτ : τ ∈ A₀ ∨ (∃ R ∈ runs, τ * (tp n R.u)⁻¹ ∈ A₀) ∨ (∃ u ∈ extra, τ * (tp n u)⁻¹ ∈ A₀)) :
    τ ∈ A₀ ∨ ∃ R ∈ runs, τ * (tp n R.u)⁻¹ ∈ A₀ := by
  rcases hτ with h | h | ⟨u, hu, hτu⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨-, hnorm, hsq⟩ := extraOK_spec hD (hextra u hu)
    set U := tp n u
    set a := τ * U⁻¹
    have hτ1 : τ * τ = 1 := by rw [← pow_two, ← hτ2, pow_orderOf_eq_one]
    apply hsq
    have h1 : (a * (U * a * U⁻¹))⁻¹ * (τ * τ) = U * U := by
      calc (a * (U * a * U⁻¹))⁻¹ * (τ * τ) = ((τ * U⁻¹) * (U * (τ * U⁻¹) * U⁻¹))⁻¹ * (τ * τ) :=
            rfl
        _ = U * U := by
            group
            exact pow_two U
    rw [← h1, hτ1, mul_one]
    exact A₀.inv_mem (A₀.mul_mem hτu (hnorm a hτu))

end CFSG.ComponentClassification.HarrisLit.P1
