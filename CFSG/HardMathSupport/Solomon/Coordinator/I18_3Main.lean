module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
open scoped commutatorElement

section Trick

variable {Q : Type*} [Group Q]

theorem i183_commutatorElement_mul_mul {a b z₁ z₂ : Q} (h1b : Commute z₁ b)
    (h12 : Commute z₁ z₂) (h2a : Commute z₂ a) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * (b * z₂) = b * z₂ * z₁ := (h1b.mul_right h12).eq
  have e2 : z₂ * a⁻¹ = a⁻¹ * z₂ := h2a.inv_right.eq
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]; group

theorem i183_commutatorElement_mul {a₁ b₁ a₂ b₂ : Q} (h1 : Commute b₁ a₂) (h2 : Commute a₁ b₂)
    (h3 : Commute ⁅b₁, b₂⁆ a₁) (h4 : Commute ⁅b₁, b₂⁆ a₂) :
    ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  have e1 : b₁ * a₂ = a₂ * b₁ := h1.eq
  have e2 : a₁⁻¹ * b₂⁻¹ = b₂⁻¹ * a₁⁻¹ := h2.inv_inv.eq
  have e3 : ⁅b₁, b₂⁆ * (a₁⁻¹ * a₂⁻¹) = (a₁⁻¹ * a₂⁻¹) * ⁅b₁, b₂⁆ :=
    (h3.inv_right.mul_right h4.inv_right).eq
  rw [commutatorElement_def] at e3
  simp only [commutatorElement_def]
  calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
      = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * (a₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by group
    _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * (b₂⁻¹ * a₁⁻¹) * a₂⁻¹ := by rw [e1, e2]
    _ = a₁ * a₂ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹ * (a₁⁻¹ * a₂⁻¹)) := by group
    _ = a₁ * a₂ * (a₁⁻¹ * a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)) := by rw [e3]
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by group

theorem i183_inv_mul_conj_mem {V : Subgroup Q} {a b s : Q} (hb : b ∈ V)
    (hs : s ∈ Subgroup.normalizer (V : Set Q)) (hab : s * (a * b) * s⁻¹ = a * b) :
    a⁻¹ * (s * a * s⁻¹) ∈ V := by
  have e : a⁻¹ * (s * a * s⁻¹) = b * (s * b * s⁻¹)⁻¹ := by
    have e' : s * a * s⁻¹ = a * b * (s * b * s⁻¹)⁻¹ := by
      calc s * a * s⁻¹ = s * (a * b) * s⁻¹ * (s * b * s⁻¹)⁻¹ := by group
        _ = a * b * (s * b * s⁻¹)⁻¹ := by rw [hab]
    rw [e']
    group
  rw [e]
  exact V.mul_mem hb (V.inv_mem ((Subgroup.mem_normalizer_iff.1 hs b).1 hb))

theorem i183_commutator_mem_centralizer {U V S : Subgroup Q}
    (hUV : U ≤ Subgroup.centralizer (V : Set Q))
    (hSU : S ≤ Subgroup.normalizer (U : Set Q)) (hSV : S ≤ Subgroup.normalizer (V : Set Q))
    {u₁ u₂ v₁ v₂ : Q} (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V)
    (h₁ : u₁ * v₁ ∈ Subgroup.centralizer (S : Set Q))
    (h₂ : u₂ * v₂ ∈ Subgroup.centralizer (S : Set Q)) :
    ⁅u₁, u₂⁆ ∈ Subgroup.centralizer (S : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have key : ∀ {u v : Q}, u ∈ U → v ∈ V → u * v ∈ Subgroup.centralizer (S : Set Q) →
      u⁻¹ * (s * u * s⁻¹) ∈ U ∧ u⁻¹ * (s * u * s⁻¹) ∈ V := by
    intro u v hu hv huv
    have hc : s * (u * v) * s⁻¹ = u * v := by
      rw [Subgroup.mem_centralizer_iff.1 huv s hs]
      group
    exact ⟨U.mul_mem (U.inv_mem hu) ((Subgroup.mem_normalizer_iff.1 (hSU hs) u).1 hu),
      i183_inv_mul_conj_mem hv (hSV hs) hc⟩
  obtain ⟨hz₁U, hz₁V⟩ := key hu₁ hv₁ h₁
  obtain ⟨hz₂U, hz₂V⟩ := key hu₂ hv₂ h₂
  have hcomm : ∀ {x y : Q}, x ∈ U → y ∈ V → Commute y x := fun hx hy =>
    Subgroup.mem_centralizer_iff.1 (hUV hx) _ hy
  have e : s * ⁅u₁, u₂⁆ * s⁻¹ = ⁅u₁, u₂⁆ := by
    calc s * ⁅u₁, u₂⁆ * s⁻¹ = ⁅s * u₁ * s⁻¹, s * u₂ * s⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅u₁ * (u₁⁻¹ * (s * u₁ * s⁻¹)), u₂ * (u₂⁻¹ * (s * u₂ * s⁻¹))⁆ := by
          simp only [mul_inv_cancel_left]
      _ = ⁅u₁, u₂⁆ := i183_commutatorElement_mul_mul (hcomm hu₂ hz₁V) (hcomm hz₂U hz₁V)
          (hcomm hu₁ hz₂V)
  calc s * ⁅u₁, u₂⁆ = s * ⁅u₁, u₂⁆ * s⁻¹ * s := by group
    _ = ⁅u₁, u₂⁆ * s := by rw [e]

theorem i183_le_sup_inf_centralizer {A₁ A₂ S Y : Subgroup Q}
    (hA : A₁ ≤ Subgroup.centralizer (A₂ : Set Q))
    (hS₁ : S ≤ Subgroup.normalizer (A₁ : Set Q)) (hS₂ : S ≤ Subgroup.normalizer (A₂ : Set Q))
    (hYA : Y ≤ A₁ ⊔ A₂) (hYS : Y ≤ Subgroup.centralizer (S : Set Q)) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ (A₁ ⊓ Subgroup.centralizer (S : Set Q)) ⊔ (A₂ ⊓ Subgroup.centralizer (S : Set Q)) := by
  have hA' : A₂ ≤ Subgroup.centralizer (A₁ : Set Q) := Subgroup.le_centralizer_iff.1 hA
  have hc : ∀ {x y : Q}, x ∈ A₁ → y ∈ A₂ → Commute x y := fun hx hy =>
    (Subgroup.mem_centralizer_iff.1 (hA hx) _ hy).symm
  rw [← hY, Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup hA (hYA hy₁)
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup hA (hYA hy₂)
  have hbb : ⁅b₁, b₂⁆ ∈ A₂ := by
    rw [commutatorElement_def]
    exact A₂.mul_mem (A₂.mul_mem (A₂.mul_mem hb₁ hb₂) (A₂.inv_mem hb₁)) (A₂.inv_mem hb₂)
  have haa : ⁅a₁, a₂⁆ ∈ A₁ := by
    rw [commutatorElement_def]
    exact A₁.mul_mem (A₁.mul_mem (A₁.mul_mem ha₁ ha₂) (A₁.inv_mem ha₁)) (A₁.inv_mem ha₂)
  have hy₁' : b₁ * a₁ ∈ Subgroup.centralizer (S : Set Q) := by
    rw [← (hc ha₁ hb₁).eq]
    exact hYS hy₁
  have hy₂' : b₂ * a₂ ∈ Subgroup.centralizer (S : Set Q) := by
    rw [← (hc ha₂ hb₂).eq]
    exact hYS hy₂
  rw [i183_commutatorElement_mul (hc ha₂ hb₁).symm (hc ha₁ hb₂) (hc ha₁ hbb).symm
    (hc ha₂ hbb).symm]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ⟨haa, i183_commutator_mem_centralizer hA hS₁ hS₂ ha₁ ha₂ hb₁ hb₂
      (hYS hy₁) (hYS hy₂)⟩)
    (Subgroup.mem_sup_right ⟨hbb, i183_commutator_mem_centralizer hA' hS₂ hS₁ hb₁ hb₂ ha₁ ha₂
      hy₁' hy₂'⟩)

end Trick

section Straddle

variable {G : Type} [Group G] [Finite G]

theorem i183_barX_le_or_le {p : ℕ} (hp : p.Prime) {X E J M₁ M₂ : Subgroup G} (hEX : E ≤ X)
    (hE : IsPGroup p ↥E) (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer (E : Set G)) J)
    (hM₁X : M₁ ≤ X) (hM₂X : M₂ ≤ X)
    (hEM₁ : E ≤ Subgroup.normalizer (M₁ : Set G)) (hEM₂ : E ≤ Subgroup.normalizer (M₂ : Set G))
    (hOM₁ : GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (M₁ : Set G))
    (hOM₂ : GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (M₂ : Set G))
    (hM₁₂ : M₁ ≤ Subgroup.normalizer (M₂ : Set G))
    (hM₂₁ : M₂ ≤ Subgroup.normalizer (M₁ : Set G))
    (hcomm : barX p X M₁ ≤ Subgroup.centralizer (barX p X M₂ : Set (↥X ⧸ GLAPPrimeCore p ↥X)))
    (hJM : J ≤ M₁ ⊔ M₂) : barX p X J ≤ barX p X M₁ ∨ barX p X J ≤ barX p X M₂ := by
  set C := X ⊓ Subgroup.centralizer (E : Set G) with hCdef
  set O := GLAPPrimeCoreOf p X with hOdef
  have hJC : J ≤ C := hJ.1
  have hCX : C ≤ X := inf_le_left
  have hJX : J ≤ X := hJC.trans hCX
  have hJE : J ≤ Subgroup.centralizer (E : Set G) := hJC.trans inf_le_right
  have hOX : O ≤ X := Subgroup.map_subtype_le _
  have hJbar : barX p X J ≤ (barX p X M₁ ⊓ Subgroup.centralizer (barX p X E : Set _)) ⊔
      (barX p X M₂ ⊓ Subgroup.centralizer (barX p X E : Set _)) := by
    refine i183_le_sup_inf_centralizer hcomm (barX_le_normalizer hEM₁) (barX_le_normalizer hEM₂)
      ((barX_mono p hJM).trans (i183_barX_sup hM₁X hM₂X).le) ?_ ?_
    · refine barX_le_centralizer fun s hs t ht _ _ => ?_
      have e : s * t * s⁻¹ * t⁻¹ = 1 := by
        rw [← Subgroup.mem_centralizer_iff.1 (hJE hs) t ht]
        group
      rw [e]
      exact Subgroup.one_mem _
    · rw [← barX_commutator p hJX hJX, glaPComponent_perfect hJ]
  have hJN : J ≤ (C ⊓ (M₁ ⊔ O)) ⊔ (C ⊓ (M₂ ⊔ O)) ⊔ (O ⊓ C) := by
    intro j hj
    have hjX := hJX hj
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hjX⟩ ∈ barX p X J :=
      ⟨⟨j, hjX⟩, hj, rfl⟩
    have hAB : barX p X M₁ ⊓ Subgroup.centralizer (barX p X E : Set _) ≤
        Subgroup.centralizer ((barX p X M₂ ⊓ Subgroup.centralizer (barX p X E : Set _) :
          Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set _) :=
      inf_le_left.trans (hcomm.trans (Subgroup.centralizer_le inf_le_left))
    obtain ⟨a, ⟨haM, haC⟩, b, ⟨hbM, hbC⟩, hab⟩ := exists_mul_of_mem_sup hAB (hJbar hmem)
    obtain ⟨c₁, hc₁, rfl⟩ := i183_centralizer_barX_le hp hEX hE haC
    obtain ⟨c₂, hc₂, rfl⟩ := i183_centralizer_barX_le hp hEX hE hbC
    have hker : (c₁ * c₂)⁻¹ * ⟨j, hjX⟩ ∈ GLAPPrimeCore p ↥X := by
      rw [← QuotientGroup.ker_mk' (GLAPPrimeCore p ↥X), MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hab]
      group
    have hoC : (((c₁ * c₂)⁻¹ * ⟨j, hjX⟩ : ↥X) : G) ∈ C :=
      C.mul_mem (C.inv_mem (C.mul_mem hc₁ hc₂)) (hJC hj)
    have e : j = (c₁ : G) * (c₂ : G) * (((c₁ * c₂)⁻¹ * ⟨j, hjX⟩ : ↥X) : G) := by
      push_cast
      group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_)
      (Subgroup.mem_sup_right ⟨⟨_, hker, rfl⟩, hoC⟩)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨hc₁, i183_mem_sup_of_mk_mem haM⟩)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨hc₂, i183_mem_sup_of_mk_mem hbM⟩)
  set H := C ⊓ (Subgroup.normalizer (M₁ : Set G) ⊓ Subgroup.normalizer (M₂ : Set G)) with hHdef
  have hHC : H ≤ C := inf_le_left
  have hHX : H ≤ X := hHC.trans hCX
  have hJH : J ≤ H := le_inf hJC (le_inf (hJM.trans (sup_le Subgroup.le_normalizer hM₂₁))
    (hJM.trans (sup_le hM₁₂ Subgroup.le_normalizer)))
  have hJ' : GLAPComponent p H J := glaPComponent_of_le hp hJ hJH hHC
  have hONX : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hHN : ∀ {M : Subgroup G}, H ≤ Subgroup.normalizer (M : Set G) →
      H ≤ Subgroup.normalizer ((C ⊓ (M ⊔ O) : Subgroup G) : Set G) := fun hM h hh =>
    i183_mem_normalizer_inf (Subgroup.le_normalizer (hHC hh))
      (i183_mem_normalizer_sup (hM hh) (hONX (hHX hh)))
  have hN₁H : C ⊓ (M₁ ⊔ O) ≤ H := le_inf inf_le_left
    (le_inf (inf_le_right.trans (sup_le Subgroup.le_normalizer hOM₁))
      (inf_le_right.trans (sup_le hM₁₂ hOM₂)))
  have hN₂H : C ⊓ (M₂ ⊔ O) ≤ H := le_inf inf_le_left
    (le_inf (inf_le_right.trans (sup_le hM₂₁ hOM₁))
      (inf_le_right.trans (sup_le Subgroup.le_normalizer hOM₂)))
  have hN₁n : ((C ⊓ (M₁ ⊔ O)).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁H).2 (hHN fun _ hh => hh.2.1)
  have hN₂n : ((C ⊓ (M₂ ⊔ O)).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₂H).2 (hHN fun _ hh => hh.2.2)
  have hO'H : O ⊓ C ≤ H := le_inf inf_le_right
    (le_inf (inf_le_left.trans hOM₁) (inf_le_left.trans hOM₂))
  have hO'core : O ⊓ C ≤ GLAPPrimeCoreOf p H := by
    have h := LocalBalance.gLAPPrimeCoreOf_inf_le hp X H
    rw [inf_eq_right.2 hHX] at h
    exact (le_inf inf_le_left hO'H).trans h
  have hbarN : ∀ {M : Subgroup G}, M ≤ X → J ≤ C ⊓ (M ⊔ O) → barX p X J ≤ barX p X M := by
    intro M hMX hJN'
    have h := barX_mono (X := X) p (hJN'.trans inf_le_right)
    rwa [i183_barX_sup hMX hOX, (i183_barX_eq_bot_iff hOX).2 le_rfl, sup_bot_eq] at h
  rcases i183_le_or_commutator_eq_bot hp hJ' hN₁H with h₁ | h₁
  · exact Or.inl (hbarN hM₁X h₁)
  rcases i183_le_or_commutator_eq_bot hp hJ' hN₂H with h₂ | h₂
  · exact Or.inr (hbarN hM₂X h₂)
  exfalso
  have hcent : barX p H J ≤ Subgroup.centralizer (barX p H J : Set (↥H ⧸ GLAPPrimeCore p ↥H)) := by
    rw [i183_barX_le_iff hJH]
    refine hJN.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact (i183_barX_le_iff hN₁H).1 (Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h₁))
    · exact (i183_barX_le_iff hN₂H).1 (Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h₂))
    · refine (i183_barX_le_iff hO'H).1 ?_
      rw [(i183_barX_eq_bot_iff hO'H).2 hO'core]
      exact bot_le
  have hbot : barX p H J = ⊥ := by
    rw [← barX_perfect_of_glaPComponent hJ']
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  have hnt := Quasisimple.nontrivial hJ'.2.2.1.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbot

end Straddle

section Main

variable {G : Type} [Group G] [Finite G]

theorem i183_transitive {p : ℕ} (hp : p.Prime) {X E J : Subgroup G} (hEX : E ≤ X)
    (hE : IsPGroup p ↥E) (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer (E : Set G)) J)
    (hJL : J ≤ GLAPLayer p X) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ i183Family p X J)
    (h₂ : L₂ ∈ i183Family p X J) : ∃ e ∈ E, GLBConj e L₁ = L₂ := by
  by_contra hno
  have hJX : J ≤ X := hJL.trans (i183_glaPLayer_le p X)
  have hJE : J ≤ Subgroup.centralizer (E : Set G) := hJ.1.trans inf_le_right
  set 𝒪 : Set (Subgroup G) := {L | ∃ e ∈ E, GLBConj e L₁ = L} with h𝒪
  set 𝒞₂ : Set (Subgroup G) := {L | L ∈ i183Family p X J ∧ L ∉ 𝒪} with h𝒞₂
  have h𝒪𝒞 : ∀ L ∈ 𝒪, L ∈ i183Family p X J := by
    rintro _ ⟨e, he, rfl⟩
    exact i183_gLBConj_mem_family hEX hJE h₁ he
  have hL₁ : L₁ ∈ 𝒪 := ⟨1, E.one_mem, gLBConj_one L₁⟩
  have hL₂ : L₂ ∈ 𝒞₂ := ⟨h₂, fun h => hno h⟩
  set M₁ := ⨆ L ∈ 𝒪, L with hM₁
  set M₂ := ⨆ L ∈ 𝒞₂, L with hM₂
  have hlay₁ : M₁ ≤ GLAPLayer p X := iSup₂_le fun L hL => le_sSup (h𝒪𝒞 L hL).1
  have hlay₂ : M₂ ≤ GLAPLayer p X := iSup₂_le fun L hL => le_sSup hL.1.1
  have hM₁X : M₁ ≤ X := hlay₁.trans (i183_glaPLayer_le p X)
  have hM₂X : M₂ ≤ X := hlay₂.trans (i183_glaPLayer_le p X)
  have hLayN₁ : GLAPLayer p X ≤ Subgroup.normalizer (M₁ : Set G) :=
    i183_le_normalizer_biSup fun L hL => i183_glaPLayer_le_normalizer hp (h𝒪𝒞 L hL).1
  have hLayN₂ : GLAPLayer p X ≤ Subgroup.normalizer (M₂ : Set G) :=
    i183_le_normalizer_biSup fun L hL => i183_glaPLayer_le_normalizer hp hL.1.1
  have hON₁ : GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (M₁ : Set G) :=
    i183_le_normalizer_biSup fun L hL => i183_glaPPrimeCoreOf_le_normalizer (h𝒪𝒞 L hL).1
  have hON₂ : GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (M₂ : Set G) :=
    i183_le_normalizer_biSup fun L hL => i183_glaPPrimeCoreOf_le_normalizer hL.1.1
  have hEN₁ : E ≤ Subgroup.normalizer (M₁ : Set G) := by
    have key : ∀ f ∈ E, GLBConj f M₁ ≤ M₁ := fun f hf =>
      i183_gLBConj_iSup_le fun L hL => by
        obtain ⟨e, he, rfl⟩ := hL
        rw [gLBConj_gLBConj]
        exact le_iSup₂_of_le _ ⟨e * f, E.mul_mem he hf, rfl⟩ le_rfl
    exact fun f hf => i183_mem_normalizer_of_gLBConj_le (key f hf) (key f⁻¹ (E.inv_mem hf))
  have hEN₂ : E ≤ Subgroup.normalizer (M₂ : Set G) := by
    have key : ∀ f ∈ E, GLBConj f M₂ ≤ M₂ := fun f hf =>
      i183_gLBConj_iSup_le fun L hL => by
        refine le_iSup₂_of_le (GLBConj f L) ⟨i183_gLBConj_mem_family hEX hJE hL.1 hf, ?_⟩ le_rfl
        rintro ⟨e, he, heq⟩
        apply hL.2
        refine ⟨e * f⁻¹, E.mul_mem he (E.inv_mem hf), ?_⟩
        rw [← gLBConj_gLBConj, heq, gLBConj_inv_gLBConj]
    exact fun f hf => i183_mem_normalizer_of_gLBConj_le (key f hf) (key f⁻¹ (E.inv_mem hf))
  have hcomm : barX p X M₁ ≤
      Subgroup.centralizer (barX p X M₂ : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [i183_barX_le_iff hM₁X]
    refine iSup₂_le fun L hL => (i183_barX_le_iff (h𝒪𝒞 L hL).1.1).1 ?_
    rw [Subgroup.le_centralizer_iff, i183_barX_le_iff hM₂X]
    refine iSup₂_le fun L' hL' => (i183_barX_le_iff hL'.1.1.1).1 ?_
    have hne : barX p X L' ≠ barX p X L := fun h => hL'.2 (by
      rw [glaPComponent_unique hL'.1.1 (h𝒪𝒞 L hL).1 h]
      exact hL)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (LocalComponents.commute_of_ne _ _ hL'.1.1.2.2.1 (h𝒪𝒞 L hL).1.2.2.1 hne)
  have hJM : J ≤ M₁ ⊔ M₂ := by
    refine (i183_le_iSup_family hp hJ hJL).trans (iSup₂_le fun L hL => ?_)
    by_cases hL𝒪 : L ∈ 𝒪
    · exact le_sup_of_le_left (le_iSup₂_of_le L hL𝒪 le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le L ⟨hL, hL𝒪⟩ le_rfl)
  rcases i183_barX_le_or_le hp hEX hE hJ hM₁X hM₂X hEN₁ hEN₂ hON₁ hON₂ (hlay₁.trans hLayN₂)
      (hlay₂.trans hLayN₁) hcomm hJM with hle | hle
  · apply h₂.2
    rw [← i183_barX_eq_bot_iff (commutator_le_of_le' hJX h₂.1.1), barX_commutator p hJX h₂.1.1,
      eq_bot_iff]
    refine (Subgroup.commutator_mono hle
      (barX_mono p (le_iSup₂_of_le L₂ hL₂ le_rfl : L₂ ≤ M₂))).trans ?_
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcomm).le
  · apply h₁.2
    rw [← i183_barX_eq_bot_iff (commutator_le_of_le' hJX h₁.1.1), barX_commutator p hJX h₁.1.1,
      eq_bot_iff]
    refine (Subgroup.commutator_mono hle
      (barX_mono p (le_iSup₂_of_le L₁ hL₁ le_rfl : L₁ ≤ M₁))).trans ?_
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcomm).le

end Main

theorem input18_3_4_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    UniquenessMaximal.Input18_3_4 := by
  intro G _ _ X hK p hp E hEX hE J hJ
  have hEp : IsPGroup p ↥E := isPGroup_of_isElemAbelian' hE
  have hJL : J ≤ GLAPLayer p X :=
    (le_sSup hJ : J ≤ GLAPLayer p (X ⊓ Subgroup.centralizer (E : Set G))).trans
      (i183_glaPLayer_inf_centralizer_le hS hK hp hEX hEp)
  exact ⟨i183Family p X J, fun L hL => hL.1, i183_iSup_family_eq hp hJ hJL,
    fun L hL e he => i183_gLBConj_mem_family hEX (hJ.1.trans inf_le_right) hL he,
    fun L hL L' hL' => i183_transitive hp hEX hEp hJ hJL hL hL'⟩

end CFSG.HardMathSupport.Solomon.Coordinator
