module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem IsSLNatSection.conj_fixV {L : Subgroup (MulAut V)} {n : ℕ}
    (h : IsSLNatSection L ⊤ (fixV L) n) (g : MulAut V) :
    IsSLNatSection (conjSub g L) ⊤ (fixV (conjSub g L)) n := by
  obtain ⟨-, θ, β, hsurj, hker, hequiv⟩ := h
  refine ⟨fun x _ p _ => trivial, ?_⟩
  let e : ↥(conjSub g L) ≃* ↥L :=
    (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let βV : V →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    β.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom
  let β' : ↥(⊤ : Subgroup V) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    (βV.comp (g⁻¹ : MulAut V).toMonoidHom).comp (Subgroup.topEquiv (G := V)).toMonoidHom
  have hβ' : ∀ p : ↥(⊤ : Subgroup V), β' p = β ⟨(g⁻¹ : MulAut V) (p : V), Subgroup.mem_top _⟩ :=
    fun p => rfl
  refine ⟨e.trans θ, β', ?_, ?_, ?_⟩
  · intro y
    obtain ⟨p, hp⟩ := hsurj y
    refine ⟨⟨g (p : V), Subgroup.mem_top _⟩, ?_⟩
    rw [hβ']
    have : (⟨(g⁻¹ : MulAut V) (g (p : V)), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = p :=
      Subtype.ext (by simp)
    rw [this]
    exact hp
  · ext p
    have h1 : β' p = 1 ↔ (g⁻¹ : MulAut V) (p : V) ∈ fixV L := by
      rw [hβ', ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker, h1, Subgroup.mem_subgroupOf, conjSub, Glauberman.fixV_map_conj]
    constructor
    · intro hp
      exact ⟨_, hp, by simp⟩
    · rintro ⟨w, hw, hwp⟩
      have : (g⁻¹ : MulAut V) (p : V) = w := by
        rw [← hwp]
        simp
      rw [this]
      exact hw
  · intro x p hp
    have hx : (x : MulAut V) = g * ((e x : ↥L) : MulAut V) * g⁻¹ := by
      have h2 : ((L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
          (e x) : ↥(L.map (MulAut.conj g).toMonoidHom)) : MulAut V) =
            (MulAut.conj g) ((e x : ↥L) : MulAut V) :=
        Subgroup.coe_equivMapOfInjective_apply _ _ _ _
      have h3 : L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
          (e x) = x := MulEquiv.apply_symm_apply _ x
      rw [h3] at h2
      rw [h2, MulAut.conj_apply]
    have hval : (g⁻¹ : MulAut V) ((x : MulAut V) (p : V)) =
        ((e x : ↥L) : MulAut V) ((g⁻¹ : MulAut V) (p : V)) := by
      rw [hx]
      simp [MulAut.mul_apply]
    have key := hequiv (e x) ⟨(g⁻¹ : MulAut V) (p : V), Subgroup.mem_top _⟩ (Subgroup.mem_top _)
    rw [hβ']
    have hsub : (⟨(g⁻¹ : MulAut V) ((x : MulAut V) (p : V)), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup V)) = ⟨((e x : ↥L) : MulAut V) ((g⁻¹ : MulAut V) (p : V)),
          Subgroup.mem_top _⟩ := Subtype.ext hval
    rw [hsub, key]
    rfl

omit [Finite V] in
theorem mSet_conjSub {P M A : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P) :
    mSet P M (conjSub g A) = conjSub g '' mSet P M A := by
  ext Y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hle⟩
    refine ⟨conjSub g⁻¹ (conjSub p M), ⟨⟨g⁻¹ * p, P.mul_mem (P.inv_mem hg) hp, ?_⟩, ?_⟩,
      FourTwoTools.conjSub_conjSub_inv g _⟩
    · rw [conjSub_mul]
    · have := conjSub_mono g⁻¹ hle
      rwa [FourTwoTools.conjSub_inv_conjSub] at this
  · rintro ⟨Y', ⟨⟨p, hp, rfl⟩, hle⟩, rfl⟩
    exact ⟨⟨g * p, P.mul_mem hg hp, by rw [conjSub_mul]⟩, conjSub_mono g hle⟩

omit [Finite V] in
theorem lamSet_conj {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M : Subgroup (MulAut V)} (h : Hyp41 P D) {L : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    {g : MulAut V} (hg : g ∈ P) : conjSub g L ∈ lamSet P D M := by
  obtain ⟨hLP, ⟨n, hn1, hSL⟩, hΛ2, hΛ3⟩ := hL
  have hinv : ∀ X ∈ dInter D (conjSub g L), conjSub g⁻¹ X ∈ dInter D L := fun X hX =>
    ⟨h.conj_mem X hX.1 g⁻¹ (P.inv_mem hg), by
      have := conjSub_mono g⁻¹ hX.2
      rwa [FourTwoTools.conjSub_inv_conjSub] at this⟩
  have hΛ2' : ∀ X : Subgroup (MulAut V), X ∈ dInter D (conjSub g L) ↔
      IsSylowOf 2 X (conjSub g L) := by
    intro X
    constructor
    · intro hX
      have h2 := isSylowOf_conjSub ((hΛ2 _).1 (hinv X hX)) g
      rwa [FourTwoTools.conjSub_conjSub_inv] at h2
    · intro hX
      have h1 : IsSylowOf 2 (conjSub g⁻¹ X) L := by
        have := isSylowOf_conjSub hX g⁻¹
        rwa [FourTwoTools.conjSub_inv_conjSub] at this
      have h2 := (hΛ2 _).2 h1
      refine ⟨?_, ?_⟩
      · have := h.conj_mem _ h2.1 g hg
        rwa [FourTwoTools.conjSub_conjSub_inv] at this
      · have := conjSub_mono g h2.2
        rwa [FourTwoTools.conjSub_conjSub_inv] at this
  refine ⟨Glauberman.map_conj_le hg hLP, ⟨n, hn1, hSL.conj_fixV g⟩, hΛ2', ?_⟩
  intro X hX Y hY hXY heq
  have hX' := hinv X hX
  have hY' := hinv Y hY
  refine hΛ3 _ hX' _ hY' (fun e => hXY ?_) ?_
  · rw [← FourTwoTools.conjSub_conjSub_inv g X, e, FourTwoTools.conjSub_conjSub_inv]
  · have h1 : mSet P M X = conjSub g '' mSet P M (conjSub g⁻¹ X) := by
      rw [← mSet_conjSub hg, FourTwoTools.conjSub_conjSub_inv]
    have h2 : mSet P M Y = conjSub g '' mSet P M (conjSub g⁻¹ Y) := by
      rw [← mSet_conjSub hg, FourTwoTools.conjSub_conjSub_inv]
    rw [h1, h2] at heq
    exact (Set.image_injective.2 (FourTwoTools.conjSub_injective g)) heq

end CFSG.CGT.PushingUpLit.BHS
