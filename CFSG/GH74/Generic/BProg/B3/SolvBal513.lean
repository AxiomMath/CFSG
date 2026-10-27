module

public import CFSG.GH74.GLS.Balance.Bender.Final

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace SolvBal

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped commutatorElement

theorem bender_l56_proved (p : ℕ) [Fact p.Prime] : BenderL56 p :=
  bender_l56 (bender_l55 (bender_l52ii p) (bender_l52iv p) (bender_l54 (bender_l53_uncond p))
    bender_q42iii bender_q43iii bender_q326)

section Basic

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem opStar_le_opStar_of_normal {A B : Subgroup G} (hAB : A ≤ B) (hn : (A.subgroupOf B).Normal) :
    OpStar p A ≤ OpStar p B := by
  refine le_opStar ((opStar_le p A).trans hAB) ?_ (isPStar_opStar (bender_l56_proved p) A)
  refine normal_subgroupOf_of_conj fun g hg x hx => ?_
  have hconj := (normal_subgroupOf_iff hAB).1 hn
  have hgA : g ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj a g ha hg, fun ha => ?_⟩
    have := hconj _ g⁻¹ ha (B.inv_mem hg)
    simpa [mul_assoc] using this
  exact opStar_conj_mem hgA hx

omit [Finite G] in
theorem map_normal_subgroupOf {A M : Subgroup G} {G' : Type} [Group G'] (f : G →* G') (hMA : M ≤ A)
    (hn : (M.subgroupOf A).Normal) : ((M.map f).subgroupOf (A.map f)).Normal := by
  refine normal_subgroupOf_of_conj ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨m, hm, rfl⟩
  refine ⟨a * m * a⁻¹, ?_, by simp⟩
  have := hn.conj_mem ⟨m, hMA hm⟩ (mem_subgroupOf.2 hm) ⟨a, ha⟩
  exact mem_subgroupOf.1 this

theorem map_opStar_le {G' : Type} [Group G'] (f : G →* G') (A : Subgroup G) :
    (OpStar p A).map f ≤ OpStar p (A.map f) := by
  refine le_opStar (map_mono (opStar_le p A)) (map_normal_subgroupOf f (opStar_le p A) inferInstance) ?_
  exact BenderExt.IsPStar.of_surjective (f.subgroupMap (OpStar p A)) (f.subgroupMap_surjective _)
    (isPStar_opStar (bender_l56_proved p) A)

theorem opStar_map_of_inf_ker {G' : Type} [Group G'] [Finite G'] (f : G →* G') {A : Subgroup G}
    (hA : A ⊓ f.ker = ⊥) : OpStar p (A.map f) = (OpStar p A).map f := by
  refine le_antisymm ?_ (map_opStar_le f A)
  set M : Subgroup G' := OpStar p (A.map f) with hM
  set M' : Subgroup G := M.comap f ⊓ A with hM'
  have hMA : M ≤ A.map f := opStar_le p _
  have hmap : M'.map f = M := by
    refine le_antisymm (fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx.1) fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hMA hy
    exact ⟨a, ⟨hy, ha⟩, rfl⟩
  have hM'A : M' ≤ A := inf_le_right
  have hinj : Function.Injective (f.comp M'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    have hm1 : (m : G) ∈ A ⊓ f.ker := ⟨hM'A m.2, hm⟩
    rw [hA, mem_bot] at hm1
    exact mem_bot.2 (Subtype.ext hm1)
  have hrange : (f.comp M'.subtype).range = M := by
    rw [← hmap]
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hM'star : IsPStar p ↥M' := by
    have e : ↥M' ≃* ↥M := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    exact IsPStar.of_mulEquiv e.symm (isPStar_opStar (bender_l56_proved p) _)
  have hM'n : (M'.subgroupOf A).Normal := by
    refine normal_subgroupOf_of_conj fun a ha x hx => ⟨?_, A.mul_mem (A.mul_mem ha hx.2) (A.inv_mem ha)⟩
    show f (a * x * a⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact opStar_conj_mem (le_normalizer (H := A.map f) (mem_map_of_mem f ha)) hx.1
  have hle : M' ≤ OpStar p A := le_opStar hM'A hM'n hM'star
  rw [← hmap]
  exact map_mono hle

omit [Finite G] in
theorem map_inf_centralizer_le {G' : Type} [Group G'] (f : G →* G') (X P : Subgroup G) :
    (X ⊓ centralizer (P : Set G)).map f ≤ X.map f ⊓ centralizer ((P.map f : Subgroup G') : Set G') := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨⟨x, hxX, rfl⟩, ?_⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hxC q hq]

omit [Finite G] in
theorem mem_normalizer_comap {G' : Type} [Group G'] (f : G →* G') {H : Subgroup G'} {g : G}
    (hg : f g ∈ normalizer (H : Set G')) : g ∈ normalizer ((H.comap f : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
  exact mem_normalizer_iff.1 hg (f h)

omit [Finite G] in
theorem mem_normalizer_opStar {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((OpStar p Y : Subgroup G) : Set G) :=
  mem_normalizer_of_conj (fun _ hx => opStar_conj_mem hg hx) (fun _ hx => opStar_conj_mem (inv_mem hg) hx)

omit [Finite G] in
theorem map_inf_centralizer_of_inf_ker {G' : Type} [Group G'] (f : G →* G') {X P : Subgroup G}
    (hXn : P ≤ normalizer (X : Set G)) (hX : X ⊓ f.ker = ⊥) :
    (X ⊓ centralizer (P : Set G)).map f =
      X.map f ⊓ centralizer ((P.map f : Subgroup G') : Set G') := by
  refine le_antisymm (map_inf_centralizer_le f X P) ?_
  · intro y hy
    obtain ⟨⟨x, hxX, rfl⟩, hxC⟩ := mem_inf.1 hy
    refine ⟨x, mem_inf.2 ⟨hxX, ?_⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro q hq
    have h1 : f q * f x = f x * f q := mem_centralizer_iff.1 hxC (f q) ⟨q, hq, rfl⟩
    have hker : q * x * q⁻¹ * x⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hmem : q * x * q⁻¹ * x⁻¹ ∈ X ⊓ f.ker :=
      mem_inf.2 ⟨X.mul_mem ((mem_normalizer_iff.1 (hXn hq) x).1 hxX) (X.inv_mem hxX), hker⟩
    rw [hX, mem_bot] at hmem
    calc q * x = (q * x * q⁻¹ * x⁻¹) * x * q := by group
      _ = x * q := by rw [hmem, one_mul]

theorem map_opStar_eq_of_inf_ker {G' : Type} [Group G'] [Finite G'] (f : G →* G') {X P : Subgroup G}
    (hXn : P ≤ normalizer (X : Set G)) (hX : X ⊓ f.ker = ⊥) :
    (OpStar p (X ⊓ centralizer (P : Set G))).map f =
      OpStar p (X.map f ⊓ centralizer ((P.map f : Subgroup G') : Set G')) := by
  rw [← map_inf_centralizer_of_inf_ker f hXn hX, opStar_map_of_inf_ker f]
  rw [eq_bot_iff]
  exact (inf_le_inf_right _ inf_le_left).trans hX.le

end Basic

section Sylow

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_isSylowIn_ge {M S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup p ↥S) :
    ∃ Q : Subgroup G, IsSylowIn p Q M ∧ S ≤ Q := by
  have hS' : IsPGroup p ↥(S.comap M.subtype) := hS.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥M).map M.subtype, isSylowIn_of_sylow p Q, fun s hs => ?_⟩
  exact ⟨⟨s, hSM hs⟩, hQ (show (⟨s, hSM hs⟩ : ↥M) ∈ S.comap M.subtype from hs), rfl⟩

theorem isSylowIn_sup_of_le {P N T : Subgroup G} [N.Normal] (hP : IsPGroup p ↥P) (hT : IsSylowIn p T N)
    (hTP : T ≤ P) : IsSylowIn p P (P ⊔ N) := by
  refine ⟨le_sup_left, hP, fun S hSM hS => ?_⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowIn_ge (M := P ⊔ N) le_sup_left hP
  have hQN : Q ⊓ N ≤ T := by
    have h1 : T ≤ Q ⊓ N := le_inf (hTP.trans hPQ) hT.1
    have h2 : Nat.card ↥(Q ⊓ N) ≤ Nat.card ↥T := hT.2.2 _ inf_le_right (hQ.2.1.to_le inf_le_left)
    exact (Subgroup.eq_of_le_of_card_ge h1 h2).symm.le
  have hQP : Q ≤ P := by
    intro g hg
    have hgM : g ∈ ((P ⊔ N : Subgroup G) : Set G) := hQ.1 hg
    rw [Subgroup.mul_normal] at hgM
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hgM
    have hbQ : b ∈ Q := by
      have : b = a⁻¹ * (a * b) := by group
      rw [this]
      exact Q.mul_mem (Q.inv_mem (hPQ ha)) hg
    exact P.mul_mem ha (hTP (hQN ⟨hbQ, hb⟩))
  exact (hQ.2.2 S hSM hS).trans (Subgroup.card_le_of_le hQP)

theorem exists_mem_mul_normalizer {M P : Subgroup G} {x : G} (hx : x ∈ normalizer (M : Set G))
    (hP : IsSylowIn p P M) : ∃ k ∈ M, k⁻¹ * x ∈ normalizer (P : Set G) := by
  have hP' : IsSylowIn p (P.map (MulAut.conj x).toMonoidHom) (M.map (MulAut.conj x).toMonoidHom) :=
    IsSylowIn.map (MulAut.conj x).injective hP
  have hMmap : M.map (MulAut.conj x).toMonoidHom = M := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hx y).mp hy
    · intro hz
      refine ⟨x⁻¹ * z * x, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp hx (x⁻¹ * z * x)).mpr (by simpa [mul_assoc] using hz)
      · simp [MulAut.conj_apply, mul_assoc]
  rw [hMmap] at hP'
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn p hP
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowIn p hP'
  obtain ⟨k, hk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj ⟨S, hS⟩ ⟨S', hS'⟩
  refine ⟨k, hk, ?_⟩
  rw [mem_normalizer_iff]
  intro w
  have h1 : x * w * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom ↔ w ∈ P := by
    constructor
    · rintro ⟨y, hy, hyw⟩
      have : y = w := by
        have h2 : x * y * x⁻¹ = x * w * x⁻¹ := hyw
        simpa using h2
      rw [← this]
      exact hy
    · intro hw
      exact ⟨w, hw, rfl⟩
  have h2 := hconj (x * w * x⁻¹)
  rw [h1] at h2
  rw [h2]
  have : k⁻¹ * (x * w * x⁻¹) * k = k⁻¹ * x * w * (k⁻¹ * x)⁻¹ := by group
  rw [this]

omit [Finite G] [Fact p.Prime] in
theorem conj_mem_sup_normal {P N : Subgroup G} [N.Normal] {g : G}
    (hg : ∀ a ∈ P, g * a * g⁻¹ ∈ P ⊔ N) {h : G} (hh : h ∈ P ⊔ N) : g * h * g⁻¹ ∈ P ⊔ N := by
  have hh' : h ∈ ((P ⊔ N : Subgroup G) : Set G) := hh
  rw [Subgroup.mul_normal] at hh'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hh'
  have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
  rw [this]
  exact mul_mem (hg a ha) (mem_sup_right ((inferInstance : N.Normal).conj_mem b hb g))

end Sylow

section Quot

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem map_frattini {X N P T : Subgroup G} [N.Normal] (hNX : N ≤ X) (hP : IsPGroup p ↥P)
    (hT : IsSylowIn p T N) (hTP : T ≤ P) :
    X.map (QuotientGroup.mk' N) ⊓ centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ≤
      (X ⊓ normalizer (P : Set G)).map (QuotientGroup.mk' N) := by
  intro z hz
  obtain ⟨⟨x, hxX, rfl⟩, hxC⟩ := mem_inf.1 hz
  have hcomm : ∀ y : G, QuotientGroup.mk' N y ∈
      centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) →
      ∀ a ∈ P, y * a * y⁻¹ ∈ P ⊔ N := by
    intro y hy a ha
    have h1 := mem_centralizer_iff.1 hy (QuotientGroup.mk' N a) ⟨a, ha, rfl⟩
    have h2 : y * a * y⁻¹ * a⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h1' : (a : G ⧸ N) * (y : G ⧸ N) = (y : G ⧸ N) * (a : G ⧸ N) := h1
      rw [← h1']
      group
    have : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (mem_sup_right h2) (mem_sup_left ha)
  have hxM : x ∈ normalizer ((P ⊔ N : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_sup_normal (hcomm x hxC) hh, fun hh => ?_⟩
    have hxC' : QuotientGroup.mk' N x⁻¹ ∈
        centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [map_inv]
      exact inv_mem hxC
    have := conj_mem_sup_normal (hcomm x⁻¹ hxC') hh
    simpa [mul_assoc] using this
  obtain ⟨k, hkM, hk⟩ := exists_mem_mul_normalizer hxM (isSylowIn_sup_of_le hP hT hTP)
  have hk' : k ∈ ((P ⊔ N : Subgroup G) : Set G) := hkM
  rw [Subgroup.mul_normal] at hk'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hk'
  set n : G := a * b * a⁻¹ with hn
  have hnN : n ∈ N := (inferInstance : N.Normal).conj_mem b hb a
  have hw : a * ((a * b)⁻¹ * x) = n⁻¹ * x := by rw [hn]; group
  refine ⟨n⁻¹ * x, mem_inf.2 ⟨X.mul_mem (X.inv_mem (hNX hnN)) hxX, ?_⟩, ?_⟩
  · rw [← hw]
    exact mul_mem (le_normalizer ha) hk
  · simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff n).2 hnN, inv_one, one_mul]

end Quot

section Minimal

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem map_opStar_eq_quot {X N : Subgroup G} [hXn : X.Normal] [hNn : N.Normal] (hX : IsPStar p ↥X)
    (hNX : N ≤ X) (hN : IsPGroup p ↥N ∨ oResOf p N = N) (hNs : IsPStar p ↥(oResOf p N)) :
    ∀ (m : ℕ) (P : Subgroup G), Nat.card G - Nat.card ↥P = m → IsPGroup p ↥P →
      (OpStar p (X ⊓ centralizer (P : Set G))).map (QuotientGroup.mk' N) =
        OpStar p (X.map (QuotientGroup.mk' N) ⊓
          centralizer ((P.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) := by
  have h56 := bender_l56_proved p
  have hXall : ∀ g : G, g ∈ normalizer (X : Set G) := fun g =>
    Subgroup.le_normalizer_of_normal (H := X) (K := ⊤) (mem_top g)
  have hNbot : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff n).2 hn
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro P hm hP
  obtain ⟨T, hTsyl, hPT⟩ := l55_exists_invariant_sylow (N := N) hP
  have hT1p : IsPGroup p ↥(T ⊓ normalizer (P : Set G)) := hTsyl.2.1.to_le inf_le_left
  have hT1N : T ⊓ normalizer (P : Set G) ≤ N := inf_le_left.trans hTsyl.1
  by_cases hT1P : T ⊓ normalizer (P : Set G) ≤ P
  ·
    have hTP : T ≤ P := le_of_inf_normalizer_le hP hTsyl.2.1 hPT hT1P
    have hB1 := map_frattini (X := X) hNX hP hTsyl hTP
    set q : G →* G ⧸ N := QuotientGroup.mk' N with hq
    set Cb : Subgroup (G ⧸ N) := X.map q ⊓ centralizer ((P.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) with hCb
    have hXbn : (X.map q).Normal := hXn.map q (QuotientGroup.mk'_surjective N)
    have hB2 : (OpStar p (X ⊓ centralizer (P : Set G))).map q ≤ OpStar p Cb := by
      refine le_opStar ((Subgroup.map_mono (opStar_le p _)).trans (map_inf_centralizer_le q X P)) ?_
        (BenderExt.IsPStar.of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
          (isPStar_opStar h56 _))
      refine normal_subgroupOf_of_conj fun z hz y hy => ?_
      obtain ⟨w, hw, rfl⟩ := hB1 hz
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨-, hwN⟩ := mem_inf.1 hw
      have hwn : w ∈ normalizer ((X ⊓ centralizer (P : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf (hXall w) (mem_normalizer_centralizer hwN)
      exact ⟨w * c * w⁻¹, opStar_conj_mem hwn hc, by simp⟩
    refine le_antisymm hB2 ?_
    set Db : Subgroup (G ⧸ N) := OpStar p Cb with hDb
    set D : Subgroup G := X ⊓ Db.comap q with hD
    have hDbX : Db ≤ X.map q := (opStar_le p Cb).trans inf_le_left
    have hDmap : D.map q = Db := by
      refine le_antisymm (fun _ ⟨x, hx, hxy⟩ => hxy ▸ (mem_inf.1 hx).2) fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := hDbX hy
      exact ⟨x, mem_inf.2 ⟨hx, hy⟩, rfl⟩
    have hND : N ≤ D := fun n hn => mem_inf.2 ⟨hNX hn, show q n ∈ Db by
      rw [hq, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
      exact one_mem _⟩
    have hDX : D ≤ X := inf_le_left
    have hNnX : (N.subgroupOf X).Normal := hNn.subgroupOf X
    have hres : oResOf p D ≤ oResOf p N ⊔ (D ⊓ centralizer (T : Set G)) := by
      refine (oResOf_le p D).trans fun y hy => ?_
      obtain ⟨n, hn, c, hc, rfl⟩ := hX.mul_centralizer hNX hNnX hTsyl y (hDX hy)
      have hcD : c ∈ D := by
        have : c = n⁻¹ * (n * c) := by group
        rw [this]
        exact D.mul_mem (D.inv_mem (hND hn)) hy
      have hcT : c ∈ D ⊓ centralizer (T : Set G) := mem_inf.2 ⟨hcD, (mem_inf.1 hc).2⟩
      rcases hN with hNp | hNeq
      · have hcen := bender_l52iv p ↥X hX (N.subgroupOf X) hNnX
          (hNp.comap_of_injective X.subtype X.subtype_injective)
        have hnT : n ∈ centralizer (T : Set G) := by
          rw [mem_centralizer_iff]
          intro t ht
          have hz := mem_center_iff.1 (hcen (show (⟨n, hNX hn⟩ : ↥X) ∈ N.subgroupOf X from hn))
            ⟨t, hNX (hTsyl.1 ht)⟩
          exact congrArg Subtype.val hz
        exact mem_sup_right (mem_inf.2 ⟨D.mul_mem (hND hn) hcD,
          (centralizer _).mul_mem hnT (mem_inf.1 hc).2⟩)
      · rw [hNeq]
        exact mul_mem_sup hn hcT
    have hNnD : (N.subgroupOf D).Normal := hNn.subgroupOf D
    have hquot : IsPStar p (↥D ⧸ N.subgroupOf D) := by
      have hker : N.subgroupOf D = (q.subgroupMap D).ker := by
        ext x
        rw [MonoidHom.mem_ker, mem_subgroupOf, ← QuotientGroup.eq_one_iff]
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      let e : (↥D ⧸ N.subgroupOf D) ≃* ↥(D.map q) :=
        (QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective D))
      have hDs : IsPStar p ↥(D.map q) := by
        rw [hDmap]
        exact isPStar_opStar h56 Cb
      exact IsPStar.of_mulEquiv e.symm hDs
    have hD0 : IsPStar p ↥(oResOf p D) := bender_l53_uncond p G D N T hND hTsyl hquot hNs hres
    have hCbn : ∀ z ∈ Cb, z ∈ normalizer ((Db : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := fun z hz =>
      mem_normalizer_opStar (le_normalizer hz)
    have hPD : P ≤ normalizer (D : Set G) := by
      intro a ha
      refine mem_normalizer_inf (hXall a) (mem_normalizer_comap q (mem_normalizer_opStar ?_))
      refine mem_normalizer_inf ?_ (mem_normalizer_centralizer (le_normalizer ⟨a, ha, rfl⟩))
      exact Subgroup.le_normalizer_of_normal (H := X.map q) (K := ⊤) (mem_top _)
    have hPD0 : P ≤ normalizer ((oResOf p D : Subgroup G) : Set G) :=
      hPD.trans (normalizer_le_normalizer_oResOf D)
    have h510 := benderT510 p G (oResOf p D) P hD0 hP hPD0
    have hcomm : ⁅oResOf p D, P⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haD : a ∈ D := oResOf_le p D ha
      have hqa : q a ∈ centralizer ((P.map q : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
        (mem_inf.1 ((opStar_le p Cb) (mem_inf.1 haD).2)).2
      rw [← QuotientGroup.eq_one_iff]
      show q ⁅a, b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 hqa (q b) ⟨b, hb, rfl⟩).symm
    have hstar : OpStar p (oResOf p D ⊓ centralizer (P : Set G)) ≤ OpStar p (X ⊓ centralizer (P : Set G)) := by
      refine opStar_le_opStar_of_normal (inf_le_inf_right _ ((oResOf_le p D).trans hDX)) ?_
      refine normal_subgroupOf_of_conj fun g hg x hx => ?_
      obtain ⟨hgX, hgC⟩ := mem_inf.1 hg
      obtain ⟨hx0, hxC⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨?_, (centralizer _).mul_mem ((centralizer _).mul_mem hgC hxC)
        ((centralizer _).inv_mem hgC)⟩
      have hgD : g ∈ normalizer (D : Set G) :=
        mem_normalizer_inf (hXall g) (mem_normalizer_comap q (hCbn _
          ((map_inf_centralizer_le q X P) ⟨g, hg, rfl⟩)))
      exact oResOf_conj_mem hgD hx0
    have hDbres : oResOf p Db = Db := (isPStar_opStar h56 Cb).oResOf_eq
    have h510' := congrArg (Subgroup.map q) h510
    calc Db = oResOf p (D.map q) := by rw [hDmap, hDbres]
      _ = (oResOf p D).map q := (BenderExt.map_oResOf (Fact.out) q D).symm
      _ ≤ (OpStar p (X ⊓ centralizer (P : Set G))).map q := by
        rw [h510', Subgroup.map_sup]
        refine sup_le ?_ (Subgroup.map_mono hstar)
        exact (Subgroup.map_mono hcomm).trans (le_of_eq hNbot) |>.trans bot_le
  ·
    set T1 : Subgroup G := T ⊓ normalizer (P : Set G) with hT1
    have hT1nP : T1 ≤ normalizer (P : Set G) := inf_le_right
    have hP'p : IsPGroup p ↥(P ⊔ T1) := by
      rw [sup_comm]
      exact isPGroup_sup_of_le_normalizer hT1p hP hT1nP
    have hlt : P < P ⊔ T1 := lt_of_le_of_ne le_sup_left fun h => hT1P (h ▸ le_sup_right)
    have hcard : Nat.card ↥P < Nat.card ↥(P ⊔ T1) := Subgroup.card_lt_of_lt hlt
    have hcardG : Nat.card ↥(P ⊔ T1) ≤ Nat.card G := Subgroup.card_le_card_group _
    have hm' : Nat.card G - Nat.card ↥(P ⊔ T1) < m := by omega
    have IH' := IH _ hm' (P ⊔ T1) rfl hP'p
    have hmapP' : (P ⊔ T1).map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) := by
      rw [Subgroup.map_sup]
      have : T1.map (QuotientGroup.mk' N) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨t, ht, rfl⟩
        exact (QuotientGroup.eq_one_iff t).2 (hT1N ht)
      rw [this, sup_bot_eq]
    rw [hmapP'] at IH'
    rw [← IH']
    set C : Subgroup G := OpStar p (X ⊓ centralizer (P : Set G)) with hC
    have hcen : X ⊓ centralizer ((P ⊔ T1 : Subgroup G) : Set G) =
        (X ⊓ centralizer (P : Set G)) ⊓ centralizer (T1 : Set G) := by
      rw [centralizer_sup_eq, inf_assoc]
    have hT1norm : T1 ≤ normalizer ((X ⊓ centralizer (P : Set G) : Subgroup G) : Set G) := fun t ht =>
      mem_normalizer_inf (hXall t) (mem_normalizer_centralizer (hT1nP ht))
    have h511 : OpStar p ((X ⊓ centralizer (P : Set G)) ⊓ centralizer (T1 : Set G)) ≤ C :=
      benderT511 p G _ T1 hT1p hT1norm
    have hT1C : T1 ≤ normalizer (C : Set G) := fun t ht => mem_normalizer_opStar (hT1norm ht)
    have h510 := benderT510 p G C T1 (isPStar_opStar h56 _) hT1p hT1C
    have hsub : OpStar p (C ⊓ centralizer (T1 : Set G)) ≤
        OpStar p ((X ⊓ centralizer (P : Set G)) ⊓ centralizer (T1 : Set G)) := by
      refine opStar_le_opStar_of_normal (inf_le_inf_right _ (opStar_le p _)) ?_
      refine normal_subgroupOf_of_conj fun g hg x hx => ?_
      obtain ⟨hg1, hg2⟩ := mem_inf.1 hg
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨opStar_conj_mem (le_normalizer hg1) hx1, ?_⟩
      exact (centralizer _).mul_mem ((centralizer _).mul_mem hg2 hx2) ((centralizer _).inv_mem hg2)
    have hcomm : ⁅C, T1⁆ ≤ N :=
      (Subgroup.commutator_mono le_rfl hT1N).trans (Subgroup.commutator_le_right C N)
    rw [hcen]
    refine le_antisymm ?_ (Subgroup.map_mono h511)
    have h510' := congrArg (Subgroup.map (QuotientGroup.mk' N)) h510
    rw [h510', Subgroup.map_sup]
    refine sup_le ?_ (Subgroup.map_mono hsub)
    exact (Subgroup.map_mono hcomm).trans (le_of_eq hNbot) |>.trans bot_le

end Minimal

section Main

variable {p : ℕ} [Fact p.Prime]

theorem card_map_lt {G G' : Type} [Group G] [Group G'] [Finite G] (f : G →* G') {H : Subgroup G}
    (h : ¬ H ⊓ f.ker = ⊥) : Nat.card ↥(H.map f) < Nat.card ↥H := by
  by_contra hle
  push Not at hle
  have hbij := (f.subgroupMap_surjective H).bijective_of_nat_card_le hle
  apply h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxk⟩ := mem_inf.1 hx
  have : f.subgroupMap H ⟨x, hxH⟩ = f.subgroupMap H 1 := by
    apply Subtype.ext
    simp only [MonoidHom.subgroupMap_apply_coe, map_one, OneMemClass.coe_one]
    exact hxk
  exact mem_bot.2 (congrArg Subtype.val (hbij.1 this))

theorem map_opStar_eq : ∀ (n : ℕ) (G : Type) [Group G] [Finite G] (G' : Type) [Group G'] [Finite G']
    (f : G →* G') (X P : Subgroup G), X.Normal → IsPStar p ↥X → IsPGroup p ↥P →
      Nat.card ↥(X ⊓ f.ker) = n →
      (OpStar p (X ⊓ centralizer (P : Set G))).map f =
        OpStar p (X.map f ⊓ centralizer ((P.map f : Subgroup G') : Set G')) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro G _ _ G' _ _ f X P hXn hX hP hn
  have hXall : ∀ g : G, g ∈ normalizer (X : Set G) := fun g =>
    Subgroup.le_normalizer_of_normal (H := X) (K := ⊤) (mem_top g)
  by_cases hbot : X ⊓ f.ker = ⊥
  · exact map_opStar_eq_of_inf_ker f (fun g _ => hXall g) hbot
  obtain ⟨N, hNn, hN1, hNle, hmin⟩ := l55_exists_minimal_normal hbot
  have hNX : N ≤ X := hNle.trans inf_le_left
  have hNk : N ≤ f.ker := hNle.trans inf_le_right
  have hresn : (oResOf p N).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hgN : g ∈ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal (H := N) (K := ⊤) (mem_top g)
    exact (mem_normalizer_iff.1 (normalizer_le_normalizer_oResOf N hgN) x).1 hx
  have hNcase : IsPGroup p ↥N ∨ oResOf p N = N := by
    rcases hmin (oResOf p N) (oResOf_le p N) hresn with h0 | h1
    · exact Or.inl (BenderExt.isPGroup_of_oResOf_eq_bot (Fact.out) h0)
    · exact Or.inr h1
  have hNs : IsPStar p ↥(oResOf p N) := by
    have h := bender_l52iii p G N hNn hN1 (fun M hMN hMn => hmin M hMN hMn)
    exact IsPStar.of_mulEquiv (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective) h
  set q : G →* G ⧸ N := QuotientGroup.mk' N with hq
  set f' : G ⧸ N →* G' := QuotientGroup.lift N f hNk with hf'
  have hcomp : f'.comp q = f := by
    ext g
    simp [hf', hq]
  have hmapq : ∀ H : Subgroup G, (H.map q).map f' = H.map f := fun H => by
    rw [Subgroup.map_map, hcomp]
  have h1 := map_opStar_eq_quot (X := X) (N := N) hX hNX hNcase hNs (Nat.card G - Nat.card ↥P) P rfl hP
  have hXq : (X.map q).Normal := hXn.map q (QuotientGroup.mk'_surjective N)
  have hXqs : IsPStar p ↥(X.map q) :=
    BenderExt.IsPStar.of_surjective (q.subgroupMap X) (q.subgroupMap_surjective X) hX
  have hker : X.map q ⊓ f'.ker = (X ⊓ f.ker).map q := by
    refine le_antisymm ?_ (fun _ ⟨x, hx, hxy⟩ => ?_)
    · intro y hy
      obtain ⟨⟨x, hxX, rfl⟩, hxk⟩ := mem_inf.1 hy
      refine ⟨x, mem_inf.2 ⟨hxX, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker] at hxk ⊢
      rw [← hcomp]
      exact hxk
    · obtain ⟨hxX, hxk⟩ := mem_inf.1 hx
      rw [← hxy]
      refine mem_inf.2 ⟨⟨x, hxX, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker] at hxk ⊢
      rw [← MonoidHom.comp_apply, hcomp]
      exact hxk
  have hlt : Nat.card ↥(X.map q ⊓ f'.ker) < n := by
    rw [hker, ← hn]
    refine card_map_lt q fun h => hN1 ?_
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (X ⊓ f.ker) ⊓ q.ker := mem_inf.2 ⟨hNle hx, by
      rw [hq, QuotientGroup.ker_mk']
      exact hx⟩
    rw [h] at this
    exact this
  have h2 := IH _ hlt (G ⧸ N) G' f' (X.map q) (P.map q) hXq hXqs (hP.map q) rfl
  rw [← hmapq, h1, h2, hmapq, hmapq]

end Main

section Prop519

theorem le_pPrimeCoreOf_of_odd' {G : Type} [Group G] {A X : Subgroup G} (hAX : A ≤ X)
    (hnorm : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hodd : Odd (Nat.card ↥A)) : A ≤ pPrimeCoreOf 2 X := by
  have hnormal : (A.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop' : Nat.Coprime 2 (Nat.card ↥(A.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : A.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
  exact Subgroup.map_mono hle

theorem map_opStar_centralizer {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] (f : G →* G') {P : Subgroup G} (hP : IsPGroup p ↥P) :
    f.range ⊓ centralizer ((P.map f : Subgroup G') : Set G') ≤
      normalizer (((OpStar p (centralizer (P : Set G))).map f : Subgroup G') : Set G') := by
  have h56 := bender_l56_proved p
  set X0 : Subgroup G := OpStar p ⊤ with hX0
  have hX0n : X0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    exact opStar_conj_mem (show g ∈ normalizer ((⊤ : Subgroup G) : Set G) by
      rw [mem_normalizer_iff]; simp) hx
  have hX0s : IsPStar p ↥X0 := isPStar_opStar h56 ⊤
  set C : Subgroup G := OpStar p (centralizer (P : Set G)) with hC
  have hCX0 : C ≤ X0 := by
    have h := benderT511 p G ⊤ P hP (fun g _ => by rw [mem_normalizer_iff]; simp)
    rwa [top_inf_eq] at h
  have hCeq : C = OpStar p (X0 ⊓ centralizer (P : Set G)) := by
    refine le_antisymm ?_ ?_
    · refine le_opStar (le_inf hCX0 (opStar_le p _)) ?_ (isPStar_opStar h56 _)
      refine normal_subgroupOf_of_conj fun g hg x hx => ?_
      exact opStar_conj_mem (le_normalizer (mem_inf.1 hg).2) hx
    · refine opStar_le_opStar_of_normal inf_le_right ?_
      refine normal_subgroupOf_of_conj fun g hg x hx => ?_
      obtain ⟨hx0, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨hX0n.conj_mem x hx0 g, (centralizer _).mul_mem ((centralizer _).mul_mem hg hxC)
        ((centralizer _).inv_mem hg)⟩
  have hmap : C.map f = OpStar p (X0.map f ⊓ centralizer ((P.map f : Subgroup G') : Set G')) := by
    rw [hCeq]
    exact map_opStar_eq _ G G' f X0 P hX0n hX0s hP rfl
  intro z hz
  obtain ⟨⟨g, -, rfl⟩, hzC⟩ := mem_inf.1 hz
  rw [hmap]
  refine mem_normalizer_opStar (mem_normalizer_inf ?_ (le_normalizer hzC))
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, hX0n.conj_mem x hx g, by simp⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g⁻¹ * x * g, by simpa using hX0n.conj_mem x hx g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hxy]
    group

theorem map_pPrimeCoreOf_centralizer_le {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (f : G →* G') {P : Subgroup G} (hP : IsPGroup 2 ↥P) :
    (pPrimeCoreOf 2 (centralizer (P : Set G))).map f ≤
      pPrimeCoreOf 2 (f.range ⊓ centralizer ((P.map f : Subgroup G') : Set G')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CP : Subgroup G := centralizer (P : Set G) with hCP
  set O : Subgroup G := pPrimeCoreOf 2 CP with hO
  set C : Subgroup G := OpStar 2 CP with hC
  set B : Subgroup G' := f.range ⊓ centralizer ((P.map f : Subgroup G') : Set G') with hB
  have hOC : O ≤ C := by
    refine le_opStar (TwoThin.pPrimeCoreOf_le CP) ?_ ?_
    · exact normal_subgroupOf_of_conj fun g hg x hx => TwoThin.pPrimeCoreOf_normalized CP hg hx
    · refine bender_l52i 2 _ ?_
      exact Nat.coprime_two_left.2 (TwoThin.card_pPrimeCoreOf_odd CP)
  have hCB : C.map f ≤ B := by
    refine le_inf ?_ ((Subgroup.map_mono (opStar_le 2 CP)).trans ?_)
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · have h := map_inf_centralizer_le f ⊤ P
      rw [top_inf_eq] at h
      exact h.trans inf_le_right
  have hBn : B ≤ normalizer ((C.map f : Subgroup G') : Set G') := map_opStar_centralizer f hP
  have hOodd : Odd (Nat.card ↥(O.map f)) := by
    have h1 := TwoThin.card_pPrimeCoreOf_odd CP
    exact Odd.of_dvd_nat h1 (Subgroup.card_map_dvd (H := O) f)
  have hO1 : O.map f ≤ pPrimeCoreOf 2 (C.map f) := by
    refine le_pPrimeCoreOf_of_odd' (Subgroup.map_mono hOC) ?_ hOodd
    rintro _ ⟨c, hc, rfl⟩ _ ⟨o, ho, rfl⟩
    refine ⟨c * o * c⁻¹, TwoThin.pPrimeCoreOf_normalized CP (opStar_le 2 CP hc) ho, by simp⟩
  have hO2 : pPrimeCoreOf 2 (C.map f) ≤ pPrimeCoreOf 2 B := by
    refine le_pPrimeCoreOf_of_odd' ((TwoThin.pPrimeCoreOf_le _).trans hCB) ?_
      (TwoThin.card_pPrimeCoreOf_odd _)
    intro b hb a ha
    exact (mem_normalizer_iff.1 (TwoThin.mem_normalizer_pPrimeCoreOf (hBn hb)) a).1 ha
  exact hO1.trans hO2

end Prop519

end SolvBal

end CFSG.GH74.Generic.BProg.B3
