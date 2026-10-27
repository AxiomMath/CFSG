module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bAbs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped Pointwise

@[expose] def K21bGeomAt (S : Type) [Group S] : Prop :=
  ∀ E U : Subgroup S, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → KFactsSmall.Permutable E U →
    E ≤ Subgroup.normalizer (U : Set S)

namespace K21bTransProof

theorem isElemAbelian_map_inj {S P : Type} [Group S] [Group P] {p : ℕ} {f : S →* P}
    (hf : Function.Injective f) {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  unfold CFSG.Open.IsElemAbelian at hE ⊢
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hxy : x * y = y * x := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

theorem mem_normalizer_of_map_inj {S P : Type} [Group S] [Group P] {f : S →* P}
    (hf : Function.Injective f) {U : Subgroup S} {x : S}
    (hx : f x ∈ Subgroup.normalizer ((U.map f : Subgroup P) : Set P)) :
    x ∈ Subgroup.normalizer (U : Set S) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  have key : ∀ z : S, f z ∈ U.map f ↔ z ∈ U := fun z => Subgroup.mem_map_iff_mem hf
  have h2 := key (x * y * x⁻¹)
  rw [map_mul, map_mul, map_inv] at h2
  exact (key y).symm.trans ((hx (f y)).trans h2)

theorem sylow_conj_exists {P : Type} [Group P] [Finite P] {U U₀ : Subgroup P}
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hU₀ : CFSG.ABGLocalTools.IsSylowOf 2 U₀ ⊤) :
    ∃ g : P, Subgroup.map (MulAut.conj g).toMonoidHom U = U₀ := by
  obtain ⟨-, hUp, hUd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hU
  obtain ⟨-, hUp₀, hUd₀⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hU₀
  rw [Subgroup.relIndex_top_right] at hUd
  rw [Subgroup.relIndex_top_right] at hUd₀
  haveI : Finite (Sylow 2 P) :=
    Finite.of_injective (fun Q : Sylow 2 P => (Q : Set P)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (hUp.toSylow hUd) (hUp₀.toSylow hUd₀)
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • U = U₀ := by
    have h2 : ((g • hUp.toSylow hUd : Sylow 2 P) : Subgroup P) =
        ((hUp₀.toSylow hUd₀ : Sylow 2 P) : Subgroup P) := by
      rw [hg]
    exact h2
  rw [← h1, Subgroup.pointwise_smul_def]
  rfl

theorem isSylowOf_top_map_mulEquiv {S P : Type} [Group S] [Group P] [Finite S] (e : S ≃* P)
    {U : Subgroup S} (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.map (e : S →* P)) ⊤ := by
  haveI : Finite P := Finite.of_equiv S e.toEquiv
  obtain ⟨-, hUp, hUd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hU
  refine (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨le_top, hUp.map (e : S →* P), ?_⟩
  rw [Subgroup.relIndex_top_right, Subgroup.index_map_equiv]
  rw [Subgroup.relIndex_top_right] at hUd
  exact hUd

end K21bTransProof

theorem K21bGeomAt.of_mulEquiv {S P : Type} [Group S] [Group P] [Finite S] (e : S ≃* P)
    (h : K21bGeomAt P) : K21bGeomAt S := by
  intro E U hE hE9 hU hperm
  have hf : Function.Injective (e : S →* P) := e.injective
  have hnorm := h (E.map (e : S →* P)) (U.map (e : S →* P))
    (K21bTransProof.isElemAbelian_map_inj hf hE)
    (by rw [Subgroup.card_map_of_injective hf]; exact hE9)
    (K21bTransProof.isSylowOf_top_map_mulEquiv e hU)
    (K21bAbsProof.permutable_map (e : S →* P) hperm)
  intro x hx
  exact K21bTransProof.mem_normalizer_of_map_inj hf
    (hnorm (Subgroup.mem_map_of_mem (e : S →* P) hx))

theorem K21bGeomAt.of_sylow {P : Type} [Group P] [Finite P] {U₀ : Subgroup P}
    (hU₀ : CFSG.ABGLocalTools.IsSylowOf 2 U₀ ⊤)
    (h : ∀ E : Subgroup P, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      KFactsSmall.Permutable E U₀ → E ≤ Subgroup.normalizer (U₀ : Set P)) : K21bGeomAt P := by
  intro E U hE hE9 hU hperm
  obtain ⟨g, hg⟩ := K21bTransProof.sylow_conj_exists hU hU₀
  have hc : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hperm' : KFactsSmall.Permutable (E.map (MulAut.conj g).toMonoidHom) U₀ := by
    rw [← hg]
    exact K21bAbsProof.permutable_map _ hperm
  have hnorm := h (E.map (MulAut.conj g).toMonoidHom)
    (K21bTransProof.isElemAbelian_map_inj hc hE)
    (by rw [Subgroup.card_map_of_injective hc]; exact hE9) hperm'
  intro x hx
  apply K21bTransProof.mem_normalizer_of_map_inj hc
  rw [hg]
  exact hnorm (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

end CFSG.LocalAnalysis.RankThreeUC.S15
