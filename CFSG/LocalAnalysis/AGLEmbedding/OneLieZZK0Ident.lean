module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapePhase
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroComp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}
  {Rb₁ : Sylow p (H₁ ⧸ primeComplementCore (G := H₁) p)}
  {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} {T₁ : Sylow p L}

theorem eq_or_unitary (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    (hCO : KFactOneLieCenterOver)
    (hZJ : centerOf ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L) ≤
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :
    ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L ∨
      (IsUnitaryGroup p L ∧
        Nat.card ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) :
          Subgroup L) = Nat.card (d1LiftX p H R K)) := by
  have hc := h.kzero
  have hd := hc.data
  have hp := h.red.prime
  have hp2 := h.red.ne_two
  set Jt := ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
    (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) with hJt
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  obtain ⟨T, -, hKcat, hTnc, hΓ, hTX⟩ := hd.exists_kFactHyps
  obtain ⟨φ₀, hφs, hφk, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  set A : Subgroup L := Jt.subgroupOf L with hA
  let ι : A ≃* Jt := Subgroup.subgroupOfEquivOfLe h.le
  set ψ : A →* K := φ₀.comp ι.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := hφs.comp ι.surjective
  have hψk : p.Coprime (Nat.card ψ.ker) := hφk.coprime_dvd_right (by
    rw [← Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ha)
  have hZA : (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ A := by
    intro x hx
    have hx' : (x : H₁ ⧸ primeComplementCore (G := H₁) p) ∈
        centerOf ((Rb₁ : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) ⊓ L) := by
      rw [← h.sylow, ← map_subtype_centerOf]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hZJ hx')
  rcases hCO K hKs hKnab hKcat p hp hp2 T hTnc hΓ hd.big L h.simple h.nonabelian h.catalog T₁
      h.sylow_noncyclic h.core_ne h.big A ψ hψs hψk hZA with htop | ⟨hU, hcard⟩
  · exact Or.inl (le_antisymm h.le (Subgroup.subgroupOf_eq_top.mp htop))
  · exact Or.inr ⟨hU, hcard.trans hTX⟩

theorem exists_mulEquiv_of_eq (h : D1OneLieKZeroComp p P M H R Rbar K P' H₁ S Rb₁ L T₁)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) :
    ∃ ψ : L ≃* K, ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, h.kzero.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩ := by
  have hc := h.kzero
  have hd := hc.data
  obtain ⟨φ, hφs, -, hφ⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  obtain ⟨-, hKnab⟩ := hd.isSimpleGroup
  have hLs : IsSimpleGroup L := h.simple
  have hJs : IsSimpleGroup (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :=
    (MulEquiv.subgroupCongr hJL).isSimpleGroup
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      apply hab
      obtain ⟨a', rfl⟩ := hφs a
      obtain ⟨b', rfl⟩ := hφs b
      have ha' : a' ∈ φ.ker := ht ▸ Subgroup.mem_top a'
      have hb' : b' ∈ φ.ker := ht ▸ Subgroup.mem_top b'
      rw [MonoidHom.mem_ker] at ha' hb'
      rw [ha', hb']
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  exact ⟨(MulEquiv.subgroupCongr hJL).symm.trans (MulEquiv.ofBijective φ ⟨hφinj, hφs⟩),
    fun j hj _ => hφ j hj⟩

end D1OneLieKZeroComp

end CFSG.AGLEmbedding
