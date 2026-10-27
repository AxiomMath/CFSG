module

public import CFSG.CGT.PushingUpLit.BHS6.SymLocalBlock

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] {n : ℕ}

section Join

theorem mem_normalizer_sSup {𝓔 : Set (Subgroup Γ)} {b : Γ}
    (h : ∀ F ∈ 𝓔, b ∈ Subgroup.normalizer (F : Set Γ)) :
    b ∈ Subgroup.normalizer ((sSup 𝓔 : Subgroup Γ) : Set Γ) := by
  have key : ∀ c : Γ, (∀ F ∈ 𝓔, ∀ x ∈ F, c * x * c⁻¹ ∈ sSup 𝓔) →
      ∀ x ∈ sSup 𝓔, c * x * c⁻¹ ∈ sSup 𝓔 := by
    intro c hc x hx
    have : sSup 𝓔 ≤ (sSup 𝓔).comap (MulAut.conj c).toMonoidHom :=
      sSup_le fun F hF y hy => hc F hF y hy
    exact this hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b (fun F hF y hy => le_sSup hF
    ((Subgroup.mem_normalizer_iff.mp (h F hF) y).mp hy)) x, fun hx => ?_⟩
  have h2 := key b⁻¹ (fun F hF y hy => le_sSup hF
    ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (h F hF)) y).mp hy)) _ hx
  simpa [mul_assoc] using h2

theorem commutator_sSup_eq {𝓔 : Set (Subgroup Γ)} {B : Subgroup Γ}
    (h : ∀ F ∈ 𝓔, ⁅F, B⁆ = F) : ⁅(sSup 𝓔 : Subgroup Γ), B⁆ = sSup 𝓔 := by
  have hn : B ≤ Subgroup.normalizer ((sSup 𝓔 : Subgroup Γ) : Set Γ) := fun b hb =>
    mem_normalizer_sSup fun F hF => by
      have := Subgroup.normalizer_commutator_ge_right F B
      rw [h F hF] at this
      exact this hb
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro e he b hb
    have h1 : b * e⁻¹ * b⁻¹ ∈ sSup 𝓔 :=
      (Subgroup.mem_normalizer_iff.mp (hn hb) e⁻¹).mp (Subgroup.inv_mem _ he)
    have h2 : ⁅e, b⁆ = e * (b * e⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact Subgroup.mul_mem _ he h1
  · refine sSup_le fun F hF => ?_
    calc F = ⁅F, B⁆ := (h F hF).symm
      _ ≤ ⁅(sSup 𝓔 : Subgroup Γ), B⁆ := Subgroup.commutator_mono (le_sSup hF) le_rfl

theorem oResidualTwo_sSup_eq_top {𝓔 : Set (Subgroup Γ)}
    (h : ∀ F ∈ 𝓔, oResidualTwo ↥F = ⊤) : oResidualTwo ↥(sSup 𝓔) = ⊤ := by
  rw [oResidualTwo_eq_top_iff]
  intro N hN hpow
  have hF : ∀ F ∈ 𝓔, F ≤ N.map (sSup 𝓔 : Subgroup Γ).subtype := by
    intro F hF
    have hFE : F ≤ sSup 𝓔 := le_sSup hF
    have hNF : (N.comap (Subgroup.inclusion hFE)).Normal := Subgroup.normal_comap _
    have hpowF : ∀ g : ↥F, ∃ k : ℕ, g ^ 2 ^ k ∈ N.comap (Subgroup.inclusion hFE) := by
      intro g
      obtain ⟨k, hk⟩ := hpow (Subgroup.inclusion hFE g)
      exact ⟨k, by simpa [map_pow] using hk⟩
    have htop := (oResidualTwo_eq_top_iff.mp (h F hF)) (N.comap (Subgroup.inclusion hFE)) hNF hpowF
    intro x hx
    refine ⟨⟨x, hFE hx⟩, ?_, rfl⟩
    have : (⟨x, hx⟩ : ↥F) ∈ N.comap (Subgroup.inclusion hFE) := by
      rw [htop]
      trivial
    exact this
  have hle : sSup 𝓔 ≤ N.map (sSup 𝓔 : Subgroup Γ).subtype := sSup_le hF
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have : z = y := Subtype.ext hzy
  rw [← this]
  exact hz

end Join

section Cover

theorem map_mem_alternating_of_oResidualTwo {G E : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
    (hE : oResidualTwo ↥E = ⊤) (hEG : E ≤ G) {e : Γ} (he : e ∈ E) :
    φ ⟨e, hEG he⟩ ∈ alternatingGroup (Fin n) := by
  have hQ : IsPGroup 2 ℤˣ := fun u => ⟨1, by simp⟩
  have := hom_eq_one_of_oResidualTwo_eq_top hE hQ
    (Equiv.Perm.sign.comp (φ.comp (Subgroup.inclusion hEG))) ⟨e, he⟩
  exact Equiv.Perm.mem_alternatingGroup.2 this

variable {G T V : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(coreMod n)}
  {T' : Set (Equiv.Perm (Fin n))}

structure SymCover (G T V : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    (T' : Set (Equiv.Perm (Fin n))) (𝓔 : Set (Subgroup Γ)) : Prop where
  block : ∀ F ∈ 𝓔, ∃ d : Equiv.Perm (Fin n), SymBlockData G T V φ d F
  cover : ∀ (t : Equiv.Perm (Fin n)) (x c : Fin n), SymTriple T' t x c →
    ∃ F ∈ 𝓔, SymBlockData G T V φ (cyc x (t x) c) F

namespace SymCover

variable {𝓔 : Set (Subgroup Γ)}

theorem le (h : SymCover G T V φ T' 𝓔) : sSup 𝓔 ≤ G :=
  sSup_le fun F hF => by
    obtain ⟨d, hd⟩ := h.block F hF
    exact hd.le

theorem residual (h : SymCover G T V φ T' 𝓔) : oResidualTwo ↥(sSup 𝓔) = ⊤ :=
  oResidualTwo_sSup_eq_top fun F hF => by
    obtain ⟨d, hd⟩ := h.block F hF
    exact hd.residual

theorem comm_le (h : SymCover G T V φ T' 𝓔) (hVn : G ≤ Subgroup.normalizer (V : Set Γ)) :
    ⁅(sSup 𝓔 : Subgroup Γ), omegaOneCenterOf (baum T)⁆ ≤ V := by
  set Z : Subgroup Γ := omegaOneCenterOf (baum T) with hZ
  let S : Subgroup Γ :=
    { carrier := {e | e ∈ G ∧ ∀ z ∈ Z, ⁅e, z⁆ ∈ V}
      one_mem' := ⟨G.one_mem, fun z _ => by simp [V.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨G.mul_mem ha hb, fun z hz => ?_⟩
        have e : ⁅a * b, z⁆ = a * ⁅b, z⁆ * a⁻¹ * ⁅a, z⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVn ha) _).mp (hb' z hz)) (ha' z hz)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨G.inv_mem ha, fun z hz => ?_⟩
        have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (hVn (G.inv_mem ha)) _).mp
          (V.inv_mem (ha' z hz))
        simpa using h1 }
  have hle : sSup 𝓔 ≤ S := sSup_le fun F hF e he => by
    obtain ⟨d, hd⟩ := h.block F hF
    exact ⟨hd.le he, fun z hz => hd.comm_le (Subgroup.commutator_mem_commutator he hz)⟩
  rw [Subgroup.commutator_le]
  intro e he z hz
  exact (hle he).2 z hz

theorem map_mem_alt (h : SymCover G T V φ T' 𝓔) {e : Γ} (he : e ∈ sSup 𝓔) :
    φ ⟨e, h.le he⟩ ∈ alternatingGroup (Fin n) :=
  map_mem_alternating_of_oResidualTwo h.residual h.le he

theorem alt_le_img (hodd : Odd n) (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) (hne : T'.Nonempty)
    (h : SymCover G T V φ T' 𝓔) : alternatingGroup (Fin n) ≤ imgG G φ (sSup 𝓔) := by
  refine alternatingGroup_le_of_cyc_mem _ hs hc hne (exists_fixed_of_swaps hodd hs hc) ?_
  intro t ht x hx c hcf
  obtain ⟨F, hF, hFd⟩ := h.cover t x c ⟨ht, hx, hcf⟩
  obtain ⟨e, he, hφe⟩ := hFd.mem_img
  exact mem_imgG.2 ⟨e, hFd.le he, le_sSup hF he, hφe⟩

theorem img_eq_alt (hodd : Odd n) (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) (hne : T'.Nonempty)
    (h : SymCover G T V φ T' 𝓔) : imgG G φ (sSup 𝓔) = alternatingGroup (Fin n) := by
  refine le_antisymm ?_ (alt_le_img hodd hs hc hne h)
  intro σ hσ
  obtain ⟨e, he, heE, rfl⟩ := mem_imgG.1 hσ
  exact h.map_mem_alt heE

theorem le_centralizer_omegaOneCenterOf (T : Subgroup Γ) :
    T ≤ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hωT : omegaOneCenterOf T ≤ Subgroup.centralizer (T : Set Γ) :=
    (Subgroup.closure_le _).2 fun x hx => hx.1.2
  exact ((Subgroup.mem_centralizer_iff.mp (hωT hw) t ht)).symm

end SymCover

variable [Finite Γ]

theorem exists_symCover (S : SymSetting G T V n φ ψ T') :
    ∃ 𝓔 : Set (Subgroup Γ), SymCover G T V φ T' 𝓔 := by
  classical
  refine ⟨{F | ∃ (t : Equiv.Perm (Fin n)) (x c : Fin n) (hτ : SymTriple T' t x c),
    F = (sym_local_block S hτ).choose}, ⟨?_, ?_⟩⟩
  · rintro F ⟨t, x, c, hτ, rfl⟩
    exact ⟨_, (sym_local_block S hτ).choose_spec⟩
  · intro t x c hτ
    exact ⟨_, ⟨t, x, c, hτ, rfl⟩, (sym_local_block S hτ).choose_spec⟩

end Cover

end CFSG.CGT.PushingUpLit.BHS6
