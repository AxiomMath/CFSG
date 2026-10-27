module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open scoped Pointwise

@[expose] def IsGomiModelFix (D : FFModel) (T₀ : Subgroup D.Gam) (m : D.Amb) : Prop :=
  ∀ t ∈ T₀, D.act t m * m⁻¹ ∈ D.ker

variable {W : Type} [CommGroup W]

section Correspondence

variable {D : FFModel} {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}
  {β : ↥I →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}

theorem mem_commModSub_iff_isGomiModelFix
    (hIinv : ∀ h : ↥L, ∀ u ∈ I, (h : MulAut W) u ∈ I)
    (hsec : ∀ γ : D.Gam, ∀ m ∈ D.sec, D.act γ m ∈ D.sec)
    (hβk : ∀ u : ↥I, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : D.Gam) (u : ↥I) (m : ↥D.sec) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ I)
      (hm : D.act γ (m : D.Amb) ∈ D.sec), β u = QuotientGroup.mk m →
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩)
    (T₀ : Subgroup D.Gam) (u : ↥I) (m : ↥D.sec) (hum : β u = QuotientGroup.mk m) :
    (u : W) ∈ commModSub I ((T₀.map π).map L.subtype) Z ↔ IsGomiModelFix D T₀ m := by
  have key : ∀ t : D.Gam, ((π t : ↥L) : MulAut W) (u : W) * (u : W)⁻¹ ∈ Z ↔
      D.act t (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker := by
    intro t
    have hu' := hIinv (π t) u u.2
    have hm' := hsec t m m.2
    rw [show ((π t : ↥L) : MulAut W) (u : W) * (u : W)⁻¹ =
      ((⟨_, hu'⟩ : ↥I) * u⁻¹ : ↥I) from rfl, ← hβk, map_mul, map_inv,
      hβe t u m hu' hm' hum, hum, mul_inv_eq_one, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := D.ker.inv_mem h
      simpa [mul_comm] using this
    · intro h
      have := D.ker.inv_mem h
      simpa [mul_comm] using this
  rw [mem_commModSub]
  constructor
  · rintro ⟨-, h⟩ t ht
    exact (key t).mp (h _ ⟨π t, ⟨t, ht, rfl⟩, rfl⟩)
  · intro h
    refine ⟨u.2, ?_⟩
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact (key t).mpr (h t ht)

end Correspondence

section Witnesses

variable {D : FFModel} {L : Subgroup (MulAut W)} {I Z : Subgroup W} {π : D.Gam →* ↥L}

private theorem smul_eq_of_forall_mem [Finite W] {s : MulAut W} {X : Subgroup W}
    (h : ∀ x ∈ X, s x ∈ X) : s • X = X := by
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact h x hx
  · exact Nat.card_le_card_of_injective
      (fun x : X => (⟨s x, Subgroup.smul_mem_pointwise_smul _ s X x.2⟩ : ↥(s • X)))
      fun a b hab => Subtype.ext (s.injective (congrArg Subtype.val hab))

private theorem smul_commModSub_eq_of_isGomiModelFix [Finite W] (hR : D.RealizesVia L I Z π)
    (T₀ : Subgroup D.Gam) {g : D.Gam}
    (hg : ∀ m ∈ D.sec, IsGomiModelFix D T₀ m → IsGomiModelFix D T₀ (D.act g m)) :
    ((π g : ↥L) : MulAut W) • commModSub I ((T₀.map π).map L.subtype) Z =
      commModSub I ((T₀.map π).map L.subtype) Z := by
  obtain ⟨-, -, -, hIinv, -, hsec, -, β, -, hβk, hβe⟩ := hR
  refine smul_eq_of_forall_mem fun x hx => ?_
  have hxI : x ∈ I := (mem_commModSub.mp hx).1
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨x, hxI⟩)
  have hfix := (mem_commModSub_iff_isGomiModelFix hIinv hsec hβk hβe T₀ ⟨x, hxI⟩ m hm.symm).mp hx
  have hu' := hIinv (π g) x hxI
  exact (mem_commModSub_iff_isGomiModelFix hIinv hsec hβk hβe T₀ ⟨_, hu'⟩ ⟨_, hsec g m m.2⟩
    (hβe g ⟨x, hxI⟩ m hu' (hsec g m m.2) hm.symm)).mpr (hg m m.2 hfix)

private theorem smul_commModSub_ne_of_isGomiModelFix (hR : D.RealizesVia L I Z π)
    (T₀ : Subgroup D.Gam) {g' : D.Gam} {m : D.Amb} (hm : m ∈ D.sec)
    (hfix : IsGomiModelFix D T₀ m) (hmove : ¬ IsGomiModelFix D T₀ (D.act g' m)) :
    ((π g' : ↥L) : MulAut W) • commModSub I ((T₀.map π).map L.subtype) Z ≠
      commModSub I ((T₀.map π).map L.subtype) Z := by
  obtain ⟨-, -, -, hIinv, -, hsec, -, β, hβs, hβk, hβe⟩ := hR
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have huX := (mem_commModSub_iff_isGomiModelFix hIinv hsec hβk hβe T₀ u ⟨m, hm⟩ hu).mpr hfix
  intro heq
  have h1 : ((π g' : ↥L) : MulAut W) (u : W) ∈ commModSub I ((T₀.map π).map L.subtype) Z := by
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ huX
  have hu' := hIinv (π g') u u.2
  exact hmove ((mem_commModSub_iff_isGomiModelFix hIinv hsec hβk hβe T₀ ⟨_, hu'⟩
    ⟨_, hsec g' m hm⟩ (hβe g' u ⟨m, hm⟩ hu' (hsec g' m hm) hu)).mp h1)

private theorem not_mem_normalizer_map (hinj : Function.Injective π) {T₀ : Subgroup D.Gam}
    {g : D.Gam} (hg : g ∉ Subgroup.normalizer (T₀ : Set D.Gam)) :
    ((π g : ↥L) : MulAut W) ∉
      Subgroup.normalizer (((T₀.map π).map L.subtype : Subgroup (MulAut W)) : Set (MulAut W)) := by
  intro h
  apply hg
  have hinj' : Function.Injective (L.subtype.comp π) := L.subtype_injective.comp hinj
  have key := Subgroup.comap_normalizer_eq_of_le_range (f := L.subtype.comp π)
    (H := T₀.map (L.subtype.comp π)) (Subgroup.map_le_range _ _)
  rw [Subgroup.comap_map_eq_self_of_injective hinj'] at key
  rw [← key, Subgroup.mem_comap, ← Subgroup.map_map]
  exact h

end Witnesses

section Conj

private theorem smul_commModSub_eq_map_conj {l : MulAut W} {I Z : Subgroup W} (hI : l • I = I)
    (hZ : l • Z = Z) (T : Subgroup (MulAut W)) :
    l • commModSub I T Z = commModSub I (T.map (MulAut.conj l).toMonoidHom) Z := by
  have hZm : ∀ y : W, l y ∈ Z ↔ y ∈ Z := fun y => by
    conv_lhs => rw [← hZ]
    exact Subgroup.smul_mem_pointwise_smul_iff
  have hIm : ∀ y : W, l y ∈ I ↔ y ∈ I := fun y => by
    conv_lhs => rw [← hI]
    exact Subgroup.smul_mem_pointwise_smul_iff
  have hc : ∀ (t : MulAut W) (x : W), (MulAut.conj l t) x * x⁻¹ =
      l (t (l⁻¹ x) * (l⁻¹ x)⁻¹) := fun t x => by
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, mem_commModSub,
    mem_commModSub]
  constructor
  · rintro ⟨hxI, hx⟩
    refine ⟨?_, ?_⟩
    · have := (hIm _).mpr hxI
      simpa using this
    · rintro _ ⟨t, ht, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hc, hZm]
      exact hx t ht
  · rintro ⟨hxI, hx⟩
    refine ⟨?_, fun t ht => ?_⟩
    · rw [← hIm]
      simpa using hxI
    · rw [← hZm, ← hc]
      exact hx _ ⟨t, ht, rfl⟩

private theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ H) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem exists_mem_map_conj_eq_of_isSylowIn {G : Type*} [Group G] [Finite G]
    {L T₁ T : Subgroup G} (h₁ : IsSylowIn 2 T₁ L) (h : IsSylowIn 2 T L) :
    ∃ l ∈ L, T = T₁.map (MulAut.conj l).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) h₁.toSylow h.toSylow
  refine ⟨g, g.2, ?_⟩
  have e : ∀ {P : Subgroup G}, P ≤ L → (P.subgroupOf L).map L.subtype = P := fun hP => by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hP]
  have hsm : ((g • h₁.toSylow : Sylow 2 ↥L) : Subgroup ↥L) =
      (h₁.toSylow : Subgroup ↥L).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  rw [← e h.le, ← IsSylowIn.coe_toSylow h, ← hg, hsm, IsSylowIn.coe_toSylow, Subgroup.map_map,
    ← e h₁.le, Subgroup.map_map]
  congr 1
  ext x
  simp

variable {L : Subgroup (MulAut W)} {I Z : Subgroup W}

private theorem natStab_map_conj (hIl : ∀ l ∈ L, l • I = I) (hZl : ∀ l ∈ L, l • Z = Z)
    {T₁ : Subgroup (MulAut W)} {l : MulAut W} (hl : l ∈ L)
    (h : L ⊓ Subgroup.normalizer (T₁ : Set (MulAut W)) <
        L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T₁ Z) ∧
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T₁ Z) < L) :
    L ⊓ Subgroup.normalizer ((T₁.map (MulAut.conj l).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) <
        L ⊓ MulAction.stabilizer (MulAut W)
          (commModSub I (T₁.map (MulAut.conj l).toMonoidHom) Z) ∧
      L ⊓ MulAction.stabilizer (MulAut W)
          (commModSub I (T₁.map (MulAut.conj l).toMonoidHom) Z) < L := by
  have hc : Function.Injective (MulAut.conj l).toMonoidHom := (MulAut.conj l).injective
  have hL : L.map (MulAut.conj l).toMonoidHom = L := map_conj_eq_self_of_mem hl
  have hN : (L ⊓ Subgroup.normalizer (T₁ : Set (MulAut W))).map (MulAut.conj l).toMonoidHom =
      L ⊓ Subgroup.normalizer ((T₁.map (MulAut.conj l).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
    rw [Subgroup.map_inf_eq _ _ _ hc, hL, Subgroup.map_equiv_normalizer_eq]
  have hS : (L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T₁ Z)).map
      (MulAut.conj l).toMonoidHom = L ⊓ MulAction.stabilizer (MulAut W)
        (commModSub I (T₁.map (MulAut.conj l).toMonoidHom) Z) := by
    rw [Subgroup.map_inf_eq _ _ _ hc, hL, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      smul_commModSub_eq_map_conj (hIl l hl) (hZl l hl)]
  rw [← hN, ← hS]
  refine ⟨(Subgroup.map_lt_map_iff_of_injective hc).mpr h.1, ?_⟩
  conv_rhs => rw [← hL]
  exact (Subgroup.map_lt_map_iff_of_injective hc).mpr h.2

end Conj

section Reduction

variable [Finite W] {L : Subgroup (MulAut W)} {I Z : Subgroup W} {D : FFModel}

omit [Finite W] in
private theorem isSylowIn_map_map [Finite D.Gam] {π : D.Gam →* ↥L} (hπs : Function.Surjective π)
    (hinj : Function.Injective π) (T₀ : Sylow 2 D.Gam) :
    IsSylowIn 2 (((T₀ : Subgroup D.Gam).map π).map L.subtype) L := by
  refine ⟨Subgroup.map_subtype_le _, (T₀.isPGroup'.map π).map L.subtype, ?_⟩
  have hidx : ((T₀ : Subgroup D.Gam).map π).index = (T₀ : Subgroup D.Gam).index :=
    Subgroup.index_map_eq (T₀ : Subgroup D.Gam) hπs
      (by rw [(MonoidHom.ker_eq_bot_iff π).mpr hinj]; exact bot_le)
  rw [Subgroup.relIndex, ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective
    L.subtype_injective, hidx]
  exact Sylow.not_dvd_index T₀

private theorem natStab_image {π : D.Gam →* ↥L} (hR : D.RealizesVia L I Z π)
    (hinj : Function.Injective π) (hIl : ∀ l ∈ L, l • I = I) (hZl : ∀ l ∈ L, l • Z = Z)
    (T₀ : Subgroup D.Gam) {g g' : D.Gam} (hg : g ∉ Subgroup.normalizer (T₀ : Set D.Gam))
    (hgfix : ∀ m ∈ D.sec, IsGomiModelFix D T₀ m → IsGomiModelFix D T₀ (D.act g m))
    {m : D.Amb} (hm : m ∈ D.sec) (hmfix : IsGomiModelFix D T₀ m)
    (hmove : ¬ IsGomiModelFix D T₀ (D.act g' m)) :
    L ⊓ Subgroup.normalizer (((T₀.map π).map L.subtype : Subgroup (MulAut W)) : Set (MulAut W)) <
        L ⊓ MulAction.stabilizer (MulAut W) (commModSub I ((T₀.map π).map L.subtype) Z) ∧
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I ((T₀.map π).map L.subtype) Z) < L := by
  have hle : L ⊓ Subgroup.normalizer (((T₀.map π).map L.subtype : Subgroup (MulAut W)) :
      Set (MulAut W)) ≤
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I ((T₀.map π).map L.subtype) Z) :=
    fun l hl => by
      obtain ⟨hlL, hlN⟩ := Subgroup.mem_inf.mp hl
      refine Subgroup.mem_inf.mpr ⟨hlL, MulAction.mem_stabilizer_iff.mpr ?_⟩
      rw [smul_commModSub hlN, hIl l hlL, hZl l hlL]
  have hgS := Subgroup.mem_inf.mpr ⟨(π g).2,
    MulAction.mem_stabilizer_iff.mpr (smul_commModSub_eq_of_isGomiModelFix hR T₀ hgfix)⟩
  have hgN : ((π g : ↥L) : MulAut W) ∉ L ⊓ Subgroup.normalizer
      (((T₀.map π).map L.subtype : Subgroup (MulAut W)) : Set (MulAut W)) :=
    fun h => not_mem_normalizer_map hinj hg (Subgroup.mem_inf.mp h).2
  have hg'S : ((π g' : ↥L) : MulAut W) ∉
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I ((T₀.map π).map L.subtype) Z) :=
    fun h => smul_commModSub_ne_of_isGomiModelFix hR T₀ hm hmfix hmove
      (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2)
  exact ⟨lt_of_le_of_ne hle fun heq => hgN (by rw [heq]; exact hgS),
    lt_of_le_of_ne inf_le_left fun heq => hg'S (by rw [heq]; exact (π g').2)⟩

theorem natStab_of_realizesVia (hD : D.Faithful) {π : D.Gam →* ↥L}
    (hR : D.RealizesVia L I Z π) (T₀ : Sylow 2 D.Gam) {g g' : D.Gam}
    (hg : g ∉ Subgroup.normalizer ((T₀ : Subgroup D.Gam) : Set D.Gam))
    (hgfix : ∀ m ∈ D.sec, IsGomiModelFix D T₀ m → IsGomiModelFix D T₀ (D.act g m))
    {m : D.Amb} (hm : m ∈ D.sec) (hmfix : IsGomiModelFix D T₀ m)
    (hmove : ¬ IsGomiModelFix D T₀ (D.act g' m)) {T : Subgroup (MulAut W)}
    (hT : IsSylowIn 2 T L) :
    L ⊓ Subgroup.normalizer (T : Set (MulAut W)) <
        L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) ∧
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) < L := by
  have hinj := FFC.injective_of_faithful_sec hD hR
  have : Finite D.Gam := Finite.of_injective π hinj
  have hR0 := hR
  obtain ⟨hπs, -, -, hIinv, hZinv, -⟩ := hR
  have hIl : ∀ l ∈ L, l • I = I := fun l hl => smul_eq_of_forall_mem fun x hx => hIinv ⟨l, hl⟩ x hx
  have hZl : ∀ l ∈ L, l • Z = Z := fun l hl => smul_eq_of_forall_mem fun x hx => hZinv ⟨l, hl⟩ x hx
  obtain ⟨l, hl, rfl⟩ := exists_mem_map_conj_eq_of_isSylowIn (isSylowIn_map_map hπs hinj T₀) hT
  exact natStab_map_conj hIl hZl hl (natStab_image hR0 hinj hIl hZl T₀ hg hgfix hm hmfix hmove)

@[expose] def GomiNatStabModel (D : FFModel) : Prop :=
  D.Faithful ∧ ∃ (T₀ : Sylow 2 D.Gam) (g g' : D.Gam) (m : D.Amb),
    g ∉ Subgroup.normalizer ((T₀ : Subgroup D.Gam) : Set D.Gam) ∧
    (∀ m' ∈ D.sec, IsGomiModelFix D T₀ m' → IsGomiModelFix D T₀ (D.act g m')) ∧
    m ∈ D.sec ∧ IsGomiModelFix D T₀ m ∧ ¬ IsGomiModelFix D T₀ (D.act g' m)

theorem natStab_of_gomiNatStabModel {T : Subgroup (MulAut W)} (hD : GomiNatStabModel D)
    (hR : D.Realizes L I Z) (hT : IsSylowIn 2 T L) :
    L ⊓ Subgroup.normalizer (T : Set (MulAut W)) <
        L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) ∧
      L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) < L := by
  obtain ⟨hF, T₀, g, g', m, hg, hgfix, hm, hmfix, hmove⟩ := hD
  obtain ⟨π, hπ⟩ := hR
  exact natStab_of_realizesVia hF hπ T₀ hg hgfix hm hmfix hmove hT

end Reduction

end CFSG.GroupTheory

end
