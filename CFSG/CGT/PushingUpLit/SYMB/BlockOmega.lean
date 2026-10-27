module

public import CFSG.CGT.PushingUpLit.SolK.NoIndexThree
public import CFSG.CGT.PushingUpLit.SolK.Vec
public import CFSG.CGT.PushingUpLit.SYMB.IHBlock
public import CFSG.CGT.PushingUpLit.SYMB.Setting

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

theorem eq_of_normalized_of_simple {M : Type*} [Group M] {A X : Subgroup M}
    [hA : IsSimpleGroup ↥A] (hXA : X ≤ A) (hXn : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hne : X ≠ ⊥) : X = A := by
  classical
  have : (X.subgroupOf A).Normal := ⟨fun x hx a => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hXn a a.2 x hx⟩
  rcases hA.eq_bot_or_eq_top_of_normal (X.subgroupOf A) with hbot | htop
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hXA hx⟩ : ↥A) ∈ X.subgroupOf A := hx
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · refine le_antisymm hXA fun a ha => ?_
    have : (⟨a, ha⟩ : ↥A) ∈ X.subgroupOf A := by
      rw [htop]
      trivial
    exact this

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}

theorem exists_block_altOn_of_simple {m : ℕ} {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
    {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}
    (S : SymSetting G T V (2 * m + 1) φ ψ T') (hih : IHFor G)
    {Ω : Finset (Fin (2 * m + 1))} (hsimple : IsSimpleGroup ↥(altOn Ω))
    (hΩ : Ω.card < 2 * m + 1) (hstab : ∀ t ∈ T', t ∈ setStab Ω)
    {t : Equiv.Perm (Fin (2 * m + 1))} (ht : t ∈ T') {x c : Fin (2 * m + 1)} (hx : t x ≠ x)
    (hcf : ∀ s ∈ T', s c = c) (hxΩ : x ∈ Ω) (htxΩ : t x ∈ Ω) (hcΩ : c ∈ Ω) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧
      imgG G φ F = altOn Ω := by
  classical
  set B : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := Subgroup.closure T' with hBdef
  set Y : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := B ⊔ altOn Ω with hYdef
  have hBstab : B ≤ setStab Ω := (Subgroup.closure_le _).2 hstab
  have hBnorm : B ≤ Subgroup.normalizer (altOn Ω : Set (Equiv.Perm (Fin (2 * m + 1)))) :=
    fun b hb => mem_normalizer_altOn_of_mem_setStab (hBstab hb)
  have hYnorm : Y ≤ Subgroup.normalizer (altOn Ω : Set (Equiv.Perm (Fin (2 * m + 1)))) :=
    sup_le hBnorm Subgroup.le_normalizer
  have hYstab : Y ≤ setStab Ω := sup_le hBstab (SolK.altOn_le_setStab Ω)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hex : ∃ b : Fin (2 * m + 1), b ∉ Ω := by
      by_contra hall
      push Not at hall
      have : Ω = Finset.univ := Finset.eq_univ_iff_forall.2 hall
      rw [this, Finset.card_univ, Fintype.card_fin] at hΩ
      omega
    obtain ⟨b, hb⟩ := hex
    have hs : Equiv.swap x b ∈ Y := by
      rw [htop]
      trivial
    have := (hYstab hs) x
    rw [Equiv.swap_apply_left] at this
    exact hb (this.2 hxΩ)
  have hsurj := S.data.φ_surj
  set L : Subgroup Γ := preimG G φ Y with hLdef
  have hLG : L ≤ G := preimG_le G φ Y
  have hLimg : imgG G φ L = Y := by
    refine le_antisymm ?_ ?_
    · intro σ hσ
      obtain ⟨g, hg, hgL, rfl⟩ := mem_imgG.1 hσ
      exact (mem_preimG.1 hgL).2
    · intro σ hσ
      obtain ⟨g, hg⟩ := hsurj σ
      refine mem_imgG.2 ⟨(g : Γ), g.2, mem_preimG.2 ⟨g.2, ?_⟩, hg⟩
      have : φ ⟨(g : Γ), g.2⟩ = σ := hg
      rw [this]
      exact hσ
  have hLlt : L < G := by
    refine lt_of_le_of_ne hLG fun heq => hYtop ?_
    rw [← hLimg, heq]
    rw [eq_top_iff]
    intro σ _
    obtain ⟨g, hg⟩ := hsurj σ
    exact mem_imgG.2 ⟨g, g.2, g.2, hg⟩
  have hBL : baum T ≤ L := by
    intro b hb
    have hbG : b ∈ G := (inf_le_left : baum T ≤ T).trans S.sylow.1 hb
    refine mem_preimG.2 ⟨hbG, ?_⟩
    have : φ ⟨b, hbG⟩ ∈ imgG G φ (baum T) := mem_imgG.2 ⟨b, hbG, hb, rfl⟩
    rw [S.baum] at this
    exact Subgroup.mem_sup_left this
  have hd : cyc x (t x) c ∈ altOn Ω := by
    have hxc : x ≠ c := fun h => hx (h ▸ hcf t ht)
    have htc : t x ≠ c := fun h => by
      have hxc' : x = c := t.injective (h.trans (hcf t ht).symm)
      exact hx (h.trans hxc'.symm)
    exact cyc_mem_altOn hxΩ htxΩ hcΩ hx.symm hxc htc
  have hLC : ¬ L ≤ cStarIn G T := by
    intro hle
    have hK : ∀ (g : Γ) (hg : g ∈ G), φ ⟨g, hg⟩ = 1 → g ∈ cStarIn G T := fun g hg h1 =>
      sym_ker_le_cStarIn S (mem_kerG.2 ⟨hg, h1⟩)
    refine not_preimG_le_cStarIn S.sylow S.ne φ hsurj S.odd hK S.nonempty S.swaps S.comm S.baum ht hx
      hcf (le_trans (preimG_mono G φ ?_) hle)
    exact sup_le (le_sup_left) (le_trans ((Subgroup.zpowers_le).2 hd) le_sup_right)
  obtain ⟨S₁, 𝒢, d⟩ := exists_ihData S.charTwo hih S.sylow ⟨hLlt, hBL, hLC⟩
  obtain ⟨F, hF, hFn⟩ := d.exists_block_not_le hLC
  set N : Subgroup Γ := ⨆ E ∈ 𝒢, E with hNdef
  have hNL : N ≤ L := d.join_le
  have hNG : N ≤ G := hNL.trans hLG
  have hB2 : IsPGroup 2 ↥B := by
    have h1 : IsPGroup 2 ↥(imgG G φ (baum T)) :=
      isPGroup_imgG ((inf_le_left : baum T ≤ T).trans S.sylow.1)
        (S.sylow.2.1.to_le inf_le_left)
    rw [S.baum] at h1
    exact h1
  have hdec : ∀ y ∈ Y, ∃ b ∈ B, ∃ δ ∈ altOn Ω, y = b * δ := by
    intro y hy
    have hmul : ((B ⊔ altOn Ω : Subgroup (Equiv.Perm (Fin (2 * m + 1)))) :
        Set (Equiv.Perm (Fin (2 * m + 1)))) = (B : Set (Equiv.Perm (Fin (2 * m + 1)))) *
        (altOn Ω : Set (Equiv.Perm (Fin (2 * m + 1)))) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B _ hBnorm
    have hy' : y ∈ ((B ⊔ altOn Ω : Subgroup (Equiv.Perm (Fin (2 * m + 1)))) :
        Set (Equiv.Perm (Fin (2 * m + 1)))) := hy
    rw [hmul] at hy'
    obtain ⟨b, hb, δ, hδ, rfl⟩ := hy'
    exact ⟨b, hb, δ, hδ, rfl⟩
  have hNY : ∀ (e : Γ) (he : e ∈ N), φ ⟨e, hNG he⟩ ∈ Y := fun e he =>
    (mem_preimG.1 (hNL he)).2
  have hNΩ : ∀ (e : Γ) (he : e ∈ N), φ ⟨e, hNG he⟩ ∈ altOn Ω :=
    map_mem_of_oResidualTwo le_sup_right hYnorm hB2 hdec d.residual_join hNG hNY
  have hNker : ¬ N ≤ kerG G φ := fun h => d.join_not_le hLC (h.trans (sym_ker_le_cStarIn S))
  have hNne : imgG G φ N ≠ ⊥ := by
    intro hbot
    apply hNker
    intro g hg
    refine mem_kerG.2 ⟨hNG hg, ?_⟩
    have : φ ⟨g, hNG hg⟩ ∈ imgG G φ N := mem_imgG.2 ⟨g, hNG hg, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hNle : imgG G φ N ≤ altOn Ω := by
    intro σ hσ
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 hσ
    exact hNΩ g hgN
  have hnormN : ∀ a ∈ altOn Ω, ∀ y ∈ imgG G φ N, a * y * a⁻¹ ∈ imgG G φ N := by
    intro a ha y hy
    have haY : a ∈ imgG G φ L := by
      rw [hLimg]
      exact Subgroup.mem_sup_right ha
    obtain ⟨l, hlG, hlL, rfl⟩ := mem_imgG.1 haY
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 hy
    have hc : l * g * l⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (d.normal_join hlL) g).mp hgN
    refine mem_imgG.2 ⟨l * g * l⁻¹, hNG hc, hc, ?_⟩
    have e : (⟨l * g * l⁻¹, hNG hc⟩ : ↥G) = ⟨l, hlG⟩ * ⟨g, hgG⟩ * ⟨l, hlG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hNeq : imgG G φ N = altOn Ω :=
    eq_of_normalized_of_simple hNle hnormN hNne
  have hFL : F ≤ L := (d.blocks F hF).le
  have hFG : F ≤ G := hFL.trans hLG
  have hFB : IsBTBlock G T F := d.isBTBlock_of_mem hLG hF hFn
  have hFN : F ≤ N := le_iSup₂ (f := fun E (_ : E ∈ 𝒢) => E) F hF
  have hFle : imgG G φ F ≤ altOn Ω := (imgG_mono G φ hFN).trans hNle
  have hFne : imgG G φ F ≠ ⊥ := by
    intro hbot
    apply hFn
    intro g hg
    apply sym_ker_le_cStarIn S
    refine mem_kerG.2 ⟨hFG hg, ?_⟩
    have : φ ⟨g, hFG hg⟩ ∈ imgG G φ F := mem_imgG.2 ⟨g, hFG hg, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hFnorm : ∀ a ∈ altOn Ω, ∀ y ∈ imgG G φ F, a * y * a⁻¹ ∈ imgG G φ F := by
    intro a ha y hy
    rw [← hNeq] at ha
    obtain ⟨g, hgG, hgN, rfl⟩ := mem_imgG.1 ha
    obtain ⟨f, hfG, hfF, rfl⟩ := mem_imgG.1 hy
    have hc : g * f * g⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (d.normalizes_block hF hgN) f).mp hfF
    refine mem_imgG.2 ⟨g * f * g⁻¹, hFG hc, hc, ?_⟩
    have e : (⟨g * f * g⁻¹, hFG hc⟩ : ↥G) = ⟨g, hgG⟩ * ⟨f, hfG⟩ * ⟨g, hgG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  exact ⟨F, hFB, hFn, eq_of_normalized_of_simple hFle hFnorm hFne⟩

theorem exists_block_altOn {m : ℕ} {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
    {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}
    (S : SymSetting G T V (2 * m + 1) φ ψ T') (hih : IHFor G)
    {Ω : Finset (Fin (2 * m + 1))} (h5 : 5 ≤ Ω.card) (hΩ : Ω.card < 2 * m + 1)
    (hstab : ∀ t ∈ T', t ∈ setStab Ω)
    {t : Equiv.Perm (Fin (2 * m + 1))} (ht : t ∈ T') {x c : Fin (2 * m + 1)} (hx : t x ≠ x)
    (hcf : ∀ s ∈ T', s c = c) (hxΩ : x ∈ Ω) (htxΩ : t x ∈ Ω) (hcΩ : c ∈ Ω) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧
      imgG G φ F = altOn Ω :=
  exists_block_altOn_of_simple S hih (SolK.isSimpleGroup_altOn h5) hΩ hstab ht hx hcf hxΩ htxΩ hcΩ

end CFSG.CGT.PushingUpLit.SYMB
