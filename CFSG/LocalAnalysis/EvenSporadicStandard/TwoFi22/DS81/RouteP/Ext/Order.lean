module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Walk
public import CFSG.Sporadic.Bridge.TwoGen

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

universe u v

section Words

theorem map_wordProd_img2 {G H : Type*} [Group G] [Group H] (φ : G →* H) (x y : G)
    (r : List (ℕ × Bool)) : φ (wordProd (img2 x y) r) = wordProd (img2 (φ x) (φ y)) r := by
  rw [map_wordProd]
  congr 1
  funext i
  unfold img2
  split_ifs <;> rfl

end Words

section FibreProduct

variable {M W : Type*} [Group M] [CommGroup W] {ρ : M →* MulAut W} {N : Type u} {N₀ : Type v}
  [Group N] [Group N₀] (X : ExtData ρ N) (X₀ : ExtData ρ N₀)

@[expose] def fibreProd : Subgroup (N × N₀) :=
  (X.π.comp (MonoidHom.fst N N₀)).eqLocus (X₀.π.comp (MonoidHom.snd N N₀))

theorem mem_fibreProd {z : N × N₀} : z ∈ fibreProd X X₀ ↔ X.π z.1 = X₀.π z.2 := Iff.rfl

@[expose] def graphE : Subgroup (N × N₀) where
  carrier := {z | X.π z.1 = 1 ∧ X₀.π z.2 = 1 ∧ X.eT z.1 = X₀.eT z.2}
  one_mem' := ⟨map_one _, map_one _, by
    simp only [Prod.fst_one, Prod.snd_one, X.eT_one, X₀.eT_one]⟩
  mul_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨X.π_eq_one_mul h1 h1', X₀.π_eq_one_mul h2 h2', ?_⟩
    simp only [Prod.mk_mul_mk] at *
    rw [X.eT_mul _ _ h1 h1', X₀.eT_mul _ _ h2 h2', h3, h3']
  inv_mem' := by
    rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    simp only [Prod.inv_mk] at *
    rw [X.eT_inv h1, X₀.eT_inv h2, h3]

theorem mem_graphE {z : N × N₀} :
    z ∈ graphE X X₀ ↔ X.π z.1 = 1 ∧ X₀.π z.2 = 1 ∧ X.eT z.1 = X₀.eT z.2 := Iff.rfl

theorem graphE_le : graphE X X₀ ≤ fibreProd X X₀ := fun z hz => by
  rw [mem_fibreProd, hz.1, hz.2.1]

theorem normal_graphE : ((graphE X X₀).subgroupOf (fibreProd X X₀)).Normal where
  conj_mem := by
    intro d hd f
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    obtain ⟨h1, h2, h3⟩ := hd
    have hf : X.π (f : N × N₀).1 = X₀.π (f : N × N₀).2 := f.2
    refine ⟨?_, ?_, ?_⟩
    · simp [h1]
    · simp [h2]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
        Prod.snd_inv]
      rw [X.eT_conj _ _ h1, X₀.eT_conj _ _ h2, h3, hf]


theorem ExtData.eq_top_of_forall_exists (T : Subgroup N) (hker : ∀ x, X.π x = 1 → x ∈ T)
    (hmap : ∀ n, ∃ t ∈ T, X.π t = X.π n) : T = ⊤ := by
  refine eq_top_iff.2 fun n _ => ?_
  obtain ⟨t, ht, htn⟩ := hmap n
  have h : t⁻¹ * n ∈ T := hker _ (by rw [map_mul, map_inv, htn, inv_mul_cancel])
  simpa using T.mul_mem ht h

theorem ExtData.exists_mem_of_closure_eq_top {a b : M}
    (hgen : Subgroup.closure ({a, b} : Set M) = ⊤) {xa xb : N} (hxa : X.π xa = a)
    (hxb : X.π xb = b) {T : Subgroup N} (ha : xa ∈ T) (hb : xb ∈ T) (n : N) :
    ∃ t ∈ T, X.π t = X.π n := by
  have hT : T.map X.π = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    rcases hg with h | h
    · exact ⟨xa, ha, by rw [hxa, h]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨xb, hb, by rw [hxb, h]⟩
  have hn : X.π n ∈ T.map X.π := hT ▸ Subgroup.mem_top _
  obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.1 hn
  exact ⟨t, ht, htn⟩

theorem exists_mulEquiv_of_subgroup {a b : M}
    (hgen : Subgroup.closure ({a, b} : Set M) = ⊤) {xa xb : N} {xa₀ xb₀ : N₀}
    (hxa : X.π xa = a) (hxb : X.π xb = b) (hxa₀ : X₀.π xa₀ = a) (hxb₀ : X₀.π xb₀ = b)
    (Γ : Subgroup (N × N₀)) (hΓF : Γ ≤ fibreProd X X₀) (hΓD : graphE X X₀ ≤ Γ)
    (hΓa : (xa, xa₀) ∈ Γ) (hΓb : (xb, xb₀) ∈ Γ)
    (hΓ1 : ∀ z ∈ Γ, X.π z.1 = 1 → z ∈ graphE X X₀) :
    ∃ Ψ : N ≃* N₀, (∀ x, X.π x = 1 → X₀.eT (Ψ x) = X.eT x) ∧ ∀ n, X₀.π (Ψ n) = X.π n := by
  have hΓ2 : ∀ z ∈ Γ, X₀.π z.2 = 1 → z ∈ graphE X X₀ := fun z hz h2 => hΓ1 z hz (by
    have h := (mem_fibreProd X X₀).1 (hΓF hz)
    rw [h, h2])
  have hs1 : ∀ n : N, ∃ z ∈ Γ, z.1 = n := by
    have hT : Γ.map (MonoidHom.fst N N₀) = ⊤ := by
      refine X.eq_top_of_forall_exists _ (fun x hx => ?_)
        (X.exists_mem_of_closure_eq_top hgen hxa hxb (T := Γ.map (MonoidHom.fst N N₀)) ?_ ?_)
      · obtain ⟨y, hy1, hy2⟩ := X₀.eT_surj (X.eT x)
        exact ⟨(x, y), hΓD ((mem_graphE X X₀).2 ⟨hx, hy1, hy2.symm⟩), rfl⟩
      · exact ⟨(xa, xa₀), hΓa, rfl⟩
      · exact ⟨(xb, xb₀), hΓb, rfl⟩
    intro n
    have hn : n ∈ Γ.map (MonoidHom.fst N N₀) := hT ▸ Subgroup.mem_top n
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hn
    exact ⟨z, hz, rfl⟩
  have hs2 : ∀ n : N₀, ∃ z ∈ Γ, z.2 = n := by
    have hT : Γ.map (MonoidHom.snd N N₀) = ⊤ := by
      refine X₀.eq_top_of_forall_exists _ (fun x hx => ?_)
        (X₀.exists_mem_of_closure_eq_top hgen hxa₀ hxb₀ (T := Γ.map (MonoidHom.snd N N₀)) ?_ ?_)
      · obtain ⟨y, hy1, hy2⟩ := X.eT_surj (X₀.eT x)
        exact ⟨(y, x), hΓD ((mem_graphE X X₀).2 ⟨hy1, hx, hy2⟩), rfl⟩
      · exact ⟨(xa, xa₀), hΓa, rfl⟩
      · exact ⟨(xb, xb₀), hΓb, rfl⟩
    intro n
    have hn : n ∈ Γ.map (MonoidHom.snd N N₀) := hT ▸ Subgroup.mem_top n
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hn
    exact ⟨z, hz, rfl⟩
  have hi1 : ∀ z ∈ Γ, z.1 = 1 → z = 1 := by
    intro z hz hz1
    obtain ⟨-, h2, h3⟩ := (mem_graphE X X₀).1 (hΓ1 z hz (by rw [hz1, map_one]))
    rw [hz1, X.eT_one] at h3
    exact Prod.ext hz1 (X₀.eT_inj z.2 1 h2 (map_one _) (by rw [← h3, X₀.eT_one]))
  have hi2 : ∀ z ∈ Γ, z.2 = 1 → z = 1 := by
    intro z hz hz2
    have h1 : X.π z.1 = 1 := by rw [(mem_fibreProd X X₀).1 (hΓF hz), hz2, map_one]
    obtain ⟨-, -, h3⟩ := (mem_graphE X X₀).1 (hΓ1 z hz h1)
    rw [hz2, X₀.eT_one] at h3
    exact Prod.ext (X.eT_inj z.1 1 h1 (map_one _) (by rw [h3, X.eT_one])) hz2
  let Φ₁ : ↥Γ →* N := (MonoidHom.fst N N₀).comp Γ.subtype
  let Φ₂ : ↥Γ →* N₀ := (MonoidHom.snd N N₀).comp Γ.subtype
  have hΦ₁ : Function.Bijective Φ₁ := by
    refine ⟨(injective_iff_map_eq_one Φ₁).2 fun z hz => Subtype.ext (hi1 z z.2 hz), fun n => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hs1 n
    exact ⟨⟨z, hz⟩, rfl⟩
  have hΦ₂ : Function.Bijective Φ₂ := by
    refine ⟨(injective_iff_map_eq_one Φ₂).2 fun z hz => Subtype.ext (hi2 z z.2 hz), fun n => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hs2 n
    exact ⟨⟨z, hz⟩, rfl⟩
  let e₁ := MulEquiv.ofBijective Φ₁ hΦ₁
  let e₂ := MulEquiv.ofBijective Φ₂ hΦ₂
  refine ⟨e₁.symm.trans e₂, fun x hx => ?_, fun n => ?_⟩
  · have h1 : ((e₁.symm x : Γ) : N × N₀).1 = x := e₁.apply_symm_apply x
    have hmem := hΓ1 _ (e₁.symm x).2 (by rw [h1]; exact hx)
    have h3 := ((mem_graphE X X₀).1 hmem).2.2
    rw [h1] at h3
    exact h3.symm
  · have h1 : ((e₁.symm n : Γ) : N × N₀).1 = n := e₁.apply_symm_apply n
    have h2 := (mem_fibreProd X X₀).1 (hΓF (e₁.symm n).2)
    rw [h1] at h2
    exact h2.symm


theorem exists_subgroup_of_bound {a b : M} (hgen : Subgroup.closure ({a, b} : Set M) = ⊤)
    {xa xb : N} {xa₀ xb₀ : N₀} (hxa : X.π xa = a) (hxb : X.π xb = b) (hxa₀ : X₀.π xa₀ = a)
    (hxb₀ : X₀.π xb₀ = b) {R : List (List (ℕ × Bool))}
    (hR : ∀ r ∈ R, wordProd (img2 a b) r = 1)
    (hmatch : ∀ r ∈ R, X.eT (wordProd (img2 xa xb) r) = X₀.eT (wordProd (img2 xa₀ xb₀) r))
    (hbound : ∀ (G : Type (max u v)) [Group G] (x y : G),
      (∀ r ∈ R, wordProd (img2 x y) r = 1) →
        ∃ H : Subgroup G, x ∈ H ∧ y ∈ H ∧ Finite H ∧ Nat.card H ≤ Nat.card M) :
    ∃ Γ : Subgroup (N × N₀), Γ ≤ fibreProd X X₀ ∧ graphE X X₀ ≤ Γ ∧ (xa, xa₀) ∈ Γ ∧
      (xb, xb₀) ∈ Γ ∧ ∀ z ∈ Γ, X.π z.1 = 1 → z ∈ graphE X X₀ := by
  classical
  set F := fibreProd X X₀ with hF
  set D : Subgroup F := (graphE X X₀).subgroupOf F with hD
  haveI : D.Normal := normal_graphE X X₀
  let q : F →* F ⧸ D := QuotientGroup.mk' D
  let πF : F →* M := X.π.comp ((MonoidHom.fst N N₀).comp F.subtype)
  have hπD : D ≤ πF.ker := fun d hd => by
    rw [MonoidHom.mem_ker]
    exact ((mem_graphE X X₀).1 (Subgroup.mem_subgroupOf.1 hd)).1
  let qπ : F ⧸ D →* M := QuotientGroup.lift D πF hπD
  have hqπ : ∀ f : F, qπ (q f) = πF f := fun f => rfl
  have hu : (xa, xa₀) ∈ F := (mem_fibreProd X X₀).2 (by rw [hxa, hxa₀])
  have hv : (xb, xb₀) ∈ F := (mem_fibreProd X X₀).2 (by rw [hxb, hxb₀])
  let u : F := ⟨(xa, xa₀), hu⟩
  let v : F := ⟨(xb, xb₀), hv⟩
  have hD_iff : ∀ f : F, q f = 1 ↔ (f : N × N₀) ∈ graphE X X₀ := fun f =>
    (QuotientGroup.eq_one_iff f).trans Subgroup.mem_subgroupOf
  have hrel : ∀ r ∈ R, wordProd (img2 (q u) (q v)) r = 1 := by
    intro r hr
    rw [← map_wordProd_img2 q u v r, hD_iff]
    have hcoe : ((wordProd (img2 u v) r : F) : N × N₀) =
        wordProd (img2 (xa, xa₀) (xb, xb₀)) r := map_wordProd_img2 F.subtype u v r
    have h1 : (wordProd (img2 (xa, xa₀) (xb, xb₀)) r).1 = wordProd (img2 xa xb) r :=
      map_wordProd_img2 (MonoidHom.fst N N₀) (xa, xa₀) (xb, xb₀) r
    have h2 : (wordProd (img2 (xa, xa₀) (xb, xb₀)) r).2 = wordProd (img2 xa₀ xb₀) r :=
      map_wordProd_img2 (MonoidHom.snd N N₀) (xa, xa₀) (xb, xb₀) r
    rw [hcoe, mem_graphE, h1, h2]
    refine ⟨?_, ?_, hmatch r hr⟩
    · rw [map_wordProd_img2, hxa, hxb]
      exact hR r hr
    · rw [map_wordProd_img2, hxa₀, hxb₀]
      exact hR r hr
  obtain ⟨H, hqu, hqv, hfin, hcard⟩ := hbound (F ⧸ D) (q u) (q v) hrel
  haveI := hfin
  have hqa : qπ (q u) = a := by rw [hqπ]; exact hxa
  have hqb : qπ (q v) = b := by rw [hqπ]; exact hxb
  have hsurj : Function.Surjective (qπ.comp H.subtype) := by
    have hT : H.map qπ = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      intro g hg
      rcases hg with h | h
      · exact ⟨q u, hqu, by rw [hqa, h]⟩
      · rw [Set.mem_singleton_iff] at h
        exact ⟨q v, hqv, by rw [hqb, h]⟩
    intro m
    have hm : m ∈ H.map qπ := hT ▸ Subgroup.mem_top m
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hm
    exact ⟨⟨h, hh⟩, rfl⟩
  have hbij := hsurj.bijective_of_nat_card_le hcard
  have hinj : ∀ f : F, q f ∈ H → X.π (f : N × N₀).1 = 1 → q f = 1 := by
    intro f hf h1
    have h : (⟨q f, hf⟩ : H) = ⟨1, H.one_mem⟩ := by
      apply hbij.1
      show qπ (q f) = qπ 1
      rw [hqπ, map_one]
      exact h1
    exact congrArg Subtype.val h
  refine ⟨(H.comap q).map F.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨f, -, rfl⟩
    exact f.2
  · intro z hz
    refine ⟨⟨z, graphE_le X X₀ hz⟩, ?_, rfl⟩
    show q ⟨z, graphE_le X X₀ hz⟩ ∈ H
    rw [(hD_iff _).2 hz]
    exact H.one_mem
  · exact ⟨u, hqu, rfl⟩
  · exact ⟨v, hqv, rfl⟩
  · rintro z ⟨f, hf, rfl⟩ h1
    exact (hD_iff f).1 (hinj f hf h1)

theorem exists_mulEquiv_of_matching_defects {a b : M}
    (hgen : Subgroup.closure ({a, b} : Set M) = ⊤) {xa xb : N} {xa₀ xb₀ : N₀}
    (hxa : X.π xa = a) (hxb : X.π xb = b) (hxa₀ : X₀.π xa₀ = a) (hxb₀ : X₀.π xb₀ = b)
    {R : List (List (ℕ × Bool))} (hR : ∀ r ∈ R, wordProd (img2 a b) r = 1)
    (hmatch : ∀ r ∈ R, X.eT (wordProd (img2 xa xb) r) = X₀.eT (wordProd (img2 xa₀ xb₀) r))
    (hbound : ∀ (G : Type (max u v)) [Group G] (x y : G),
      (∀ r ∈ R, wordProd (img2 x y) r = 1) →
        ∃ H : Subgroup G, x ∈ H ∧ y ∈ H ∧ Finite H ∧ Nat.card H ≤ Nat.card M) :
    ∃ Ψ : N ≃* N₀, (∀ x, X.π x = 1 → X₀.eT (Ψ x) = X.eT x) ∧ ∀ n, X₀.π (Ψ n) = X.π n := by
  obtain ⟨Γ, h1, h2, h3, h4, h5⟩ :=
    exists_subgroup_of_bound X X₀ hgen hxa hxb hxa₀ hxb₀ hR hmatch hbound
  exact exists_mulEquiv_of_subgroup X X₀ hgen hxa hxb hxa₀ hxb₀ Γ h1 h2 h3 h4 h5

end FibreProduct

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
