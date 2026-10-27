module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltExc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LieType.BorelTits

variable {K' : Type} [Group K'] [Finite K'] {q : ℕ} [Fact q.Prime]

theorem pCoreOf_normalizer_map_center (Γ : Subgroup (MulAut K')) {Q : Subgroup K'}
    (hQp : IsPGroup q ↥Q) (hinv : ∀ g ∈ Γ, Q.map g.toMonoidHom = Q)
    (hmax : ∀ T : Subgroup K', IsPGroup q ↥T → (∀ g ∈ Γ, T.map g.toMonoidHom = T) → Q ≤ T →
      T = Q) :
    pCoreOf q (Subgroup.normalizer
        ((Q.map (QuotientGroup.mk' (Subgroup.center K')) : Subgroup (K' ⧸ Subgroup.center K')) :
          Set (K' ⧸ Subgroup.center K'))) =
      Q.map (QuotientGroup.mk' (Subgroup.center K')) := by
  classical
  set Z := Subgroup.center K' with hZ
  set π : K' →* K' ⧸ Z := QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  set Qb : Subgroup (K' ⧸ Z) := Q.map π with hQb
  set Rb : Subgroup (K' ⧸ Z) := pCoreOf q (Subgroup.normalizer (Qb : Set (K' ⧸ Z))) with hRb
  have hQbp : IsPGroup q ↥Qb := hQp.map π
  have hQbR : Qb ≤ Rb := le_pCoreOf_of_le_normalizer q Subgroup.le_normalizer le_rfl hQbp
  refine le_antisymm ?_ hQbR
  let ĝ : MulAut K' → MulAut (K' ⧸ Z) := fun g =>
    QuotientGroup.congr Z Z g (map_center_mulEquiv g)
  have hĝπ : ∀ g x, ĝ g (π x) = π (g x) := fun g x => rfl
  have hĝQ : ∀ g ∈ Γ, Qb.map (ĝ g).toMonoidHom = Qb := by
    intro g hg
    have hc : (ĝ g).toMonoidHom.comp π = π.comp g.toMonoidHom := by ext x; rfl
    rw [hQb, Subgroup.map_map, hc, ← Subgroup.map_map, hinv g hg]
  have hĝR : ∀ g ∈ Γ, Rb.map (ĝ g).toMonoidHom = Rb := by
    intro g hg
    rw [hRb, ← pCoreOf_map_mulEquiv q (ĝ g), Subgroup.map_equiv_normalizer_eq, hĝQ g hg]
  set M : Subgroup K' := Rb.comap π with hMdef
  have hMπ : ∀ x, x ∈ M ↔ π x ∈ Rb := fun x => Iff.rfl
  have hMg : ∀ g ∈ Γ, ∀ x, x ∈ M ↔ g x ∈ M := by
    intro g hg x
    rw [hMπ, hMπ, ← hĝπ]
    constructor
    · intro hx
      have : ĝ g (π x) ∈ Rb.map (ĝ g).toMonoidHom := ⟨π x, hx, rfl⟩
      rwa [hĝR g hg] at this
    · intro hx
      rw [← hĝR g hg] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = π x := (ĝ g).injective hyx
      rwa [← this]
  let f : ↥M →* ↥Rb := (π.comp M.subtype).codRestrict Rb (fun x => x.2)
  have hfsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨x, hx⟩ := hπ r
    exact ⟨⟨x, show π x ∈ Rb by rw [hx]; exact hr⟩, Subtype.ext hx⟩
  have hfker : f.ker ≤ Subgroup.center ↥M := by
    intro x hx
    have h1 : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hxZ : (x : K') ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxZ (y : K'))
  haveI : Group.IsNilpotent ↥Rb := (pCoreOf_isPGroup q _).isNilpotent
  haveI : Group.IsNilpotent ↥M := Subgroup.isNilpotent_of_ker_le_center f hfker
  obtain ⟨P⟩ : Nonempty (Sylow q ↥M) := inferInstance
  haveI hPn : (P : Subgroup ↥M).Normal := inferInstance
  haveI hU : Unique (Sylow q ↥M) := Sylow.unique_of_normal P hPn
  let T : Subgroup K' := (P : Subgroup ↥M).map M.subtype
  have hTp : IsPGroup q ↥T := P.isPGroup'.map M.subtype
  have hTmem : ∀ x : K', x ∈ T ↔ x ∈ M ∧ ∃ k : ℕ, x ^ q ^ k = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
      refine ⟨k, ?_⟩
      have h1 := congrArg (fun z : ↥(P : Subgroup ↥M) => ((z : ↥M) : K')) hk
      simpa using h1
    · rintro ⟨hxM, k, hk⟩
      let y : ↥M := ⟨x, hxM⟩
      have hy : y ^ q ^ k = 1 := Subtype.ext (by simpa using hk)
      have hyp : IsPGroup q ↥(Subgroup.zpowers y) := by
        intro g
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
        refine ⟨k, Subtype.ext ?_⟩
        show (g : ↥M) ^ q ^ k = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
      obtain ⟨P', hP'⟩ := IsPGroup.exists_le_sylow hyp
      have hP'P : P' = P := Subsingleton.elim _ _
      subst hP'P
      exact ⟨y, hP' (Subgroup.mem_zpowers y), rfl⟩
  have hTpres : ∀ g ∈ Γ, ∀ t ∈ T, g t ∈ T := by
    intro g hg t ht
    obtain ⟨htM, k, hk⟩ := (hTmem t).1 ht
    refine (hTmem _).2 ⟨(hMg g hg t).1 htM, k, ?_⟩
    rw [← map_pow, hk, map_one]
  have hTinv : ∀ g ∈ Γ, T.map g.toMonoidHom = T := by
    intro g hg
    refine le_antisymm ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact hTpres g hg t ht
    · intro t ht
      refine ⟨g⁻¹ t, hTpres g⁻¹ (Γ.inv_mem hg) t ht, ?_⟩
      exact MulAut.apply_inv_self K' g t
  have hQT : Q ≤ T := by
    intro x hx
    refine (hTmem x).2 ⟨?_, ?_⟩
    · exact hQbR ⟨x, hx, rfl⟩
    · obtain ⟨k, hk⟩ := hQp ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hTQ : T = Q := hmax T hTp hTinv hQT
  have hfP : (P : Subgroup ↥M).map f = ⊤ := by
    have hc : (↑(Sylow.mapSurjective hfsurj P) : Subgroup ↥Rb) = (P : Subgroup ↥M).map f :=
      Sylow.coe_mapSurjective hfsurj P
    rw [← hc]
    have hRbp : IsPGroup q ↥Rb := pCoreOf_isPGroup q _
    have hTop : IsPGroup q ↥(⊤ : Subgroup ↥Rb) := hRbp.of_equiv Subgroup.topEquiv.symm
    exact ((Sylow.mapSurjective hfsurj P).is_maximal' hTop le_top).symm
  intro r hr
  obtain ⟨y, hy, hyr⟩ : ∃ y ∈ (P : Subgroup ↥M), f y = ⟨r, hr⟩ := by
    have : (⟨r, hr⟩ : ↥Rb) ∈ (P : Subgroup ↥M).map f := by rw [hfP]; trivial
    exact this
  have hyT : (y : K') ∈ T := ⟨y, hy, rfl⟩
  rw [hTQ] at hyT
  exact ⟨(y : K'), hyT, congrArg Subtype.val hyr⟩

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
