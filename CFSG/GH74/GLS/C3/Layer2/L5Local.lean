module

public import CFSG.GH74.GLS.C3.Layer2.L5Loc
public import CFSG.GH74.GLS.C3.Layer2.L5Star9
public import CFSG.GH74.GLS.C3.Layer2.L5Abs

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

namespace Loc5

variable {h : IsAConfig 5 x K T Q S a} (L : Loc5 h)
include L

@[expose] def RS : Subgroup G := (Rc9.comap L.ψ).map S.subtype

theorem mem_RS
    {y : G} : y ∈ L.RS ↔ ∃ hy : y ∈ S, L.ψ ⟨y, hy⟩ ∈ Rc9 := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hy, hψ⟩
    exact ⟨⟨y, hy⟩, hψ, rfl⟩

theorem RS_le_S : L.RS ≤ S := by
  rintro y ⟨s, -, rfl⟩
  exact s.2

theorem EG_inf_RS : L.EG ⊓ L.RS = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyE, hyR⟩
  obtain ⟨hyS, hψE⟩ := L.mem_EG.1 hyE
  obtain ⟨hyS', hψR⟩ := L.mem_RS.1 hyR
  have h1 : L.ψ ⟨y, hyS⟩ ∈ E9 ⊓ Rc9 := ⟨hψE, hψR⟩
  rw [E9_inf_Rc9, Subgroup.mem_bot] at h1
  have h2 : (⟨y, hyS⟩ : ↥S) = 1 := L.hψ.inj (h1.trans (map_one _).symm)
  have h3 := congrArg Subtype.val h2
  rw [Subgroup.mem_bot]
  exact h3

theorem EG_sup_RS :
    L.EG ⊔ L.RS = S := by
  apply le_antisymm (sup_le L.EG_le_S L.RS_le_S)
  intro s hs
  have hs0 : L.ψ ⟨s, hs⟩ ∈ S0l := mem_S0l.2 (L.hψ.mem ⟨s, hs⟩)
  obtain ⟨e, he, r, hr, hsplit⟩ := S0_split_aux _ hs0
  obtain ⟨s₁, hs₁⟩ := L.hψ.surj e (E9_le_S0 (mem_E9l.1 he))
  obtain ⟨s₂, hs₂⟩ := L.hψ.surj r (Rc9_le_S0 hr)
  have h1 : (⟨s, hs⟩ : ↥S) = s₁ * s₂ := by
    apply L.hψ.inj
    rw [map_mul, hs₁, hs₂]
    exact hsplit
  have h2 : s = (s₁ : G) * (s₂ : G) := congrArg Subtype.val h1
  rw [h2]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
  · exact L.mem_EG.2 ⟨s₁.2, by rw [hs₁]; exact mem_E9l.1 he⟩
  · exact L.mem_RS.2 ⟨s₂.2, by rw [hs₂]; exact hr⟩

theorem normalizer_EG5
    (hZD : CFSG.GH74.Uniqueness.S_ZD) :
    ∀ g : G, g * L4.vElt x a = L4.vElt x a * g → ∀ e ∈ L.EG, g * e * g⁻¹ ∈ L.EG := by
  have hTS : T ≤ S := h.T_lt_S.le
  set Cv : Subgroup G := centralizer ({L4.vElt x a} : Set G) with hCv
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * L4.vElt x a = L4.vElt x a * g := fun g =>
    mem_centralizer_singleton_iff
  have hSCv : S ≤ Cv := by
    intro s hs
    rw [hmemCv]
    have h1 := congrArg Subtype.val (L.hψ.v_cent ⟨s, hs⟩)
    exact h1
  have hEgT : L.EG ≤ T := L.EG_le_T
  have hEgCv : L.EG ≤ Cv := hEgT.trans (L4.T_le_centralizer_v h)
  let v' : ↥Cv := ⟨L4.vElt x a, (hmemCv _).2 rfl⟩
  let x' : ↥Cv := ⟨x, L4.x_mem_centralizer_v h⟩
  let a' : ↥Cv := ⟨a, L4.a_mem_centralizer_v h⟩
  let Zs : Set ↥Cv := {z | ∃ g : ↥Cv, g * x' * g⁻¹ = z}
  let S' : Subgroup ↥Cv := S.subgroupOf Cv
  let E' : Subgroup ↥Cv := L.EG.subgroupOf Cv
  have hx'sq : x' * x' = 1 := Subtype.ext (L4.x_mul_self h)
  have hx'v : x' * v' = a' * x' * a'⁻¹ := Subtype.ext (L4.x_mul_v h)
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hZmv : ∀ z ∈ Zs, z * v' ∈ Zs := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * a', ?_⟩
    calc g * a' * x' * (g * a')⁻¹ = g * (a' * x' * a'⁻¹) * g⁻¹ := by group
      _ = g * (x' * v') * g⁻¹ := by rw [hx'v]
      _ = g * x' * (v' * g⁻¹) := by group
      _ = g * x' * (g⁻¹ * v') := by rw [← hv'c g⁻¹]
      _ = g * x' * g⁻¹ * v' := by group
  have hconjord : ∀ g : ↥Cv, orderOf ((g : G) * x * (g : G)⁻¹) = 2 := by
    intro g
    have := MulEquiv.orderOf_eq (MulAut.conj (g : G)) x
    simpa [MulAut.conj_apply, h.x_order] using this
  have hTI : L4.TIData v' Zs S' E' x' := by
    refine ⟨?_, ?_, hv'c, ?_, ?_, ?_, ?_, hZmv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.ext (L4.v_mul_self h)
    · exact fun h1 => L4.v_ne_one h (congrArg Subtype.val h1)
    · rintro _ ⟨g, rfl⟩
      calc g * x' * g⁻¹ * (g * x' * g⁻¹) = g * (x' * x') * g⁻¹ := by group
        _ = 1 := by rw [hx'sq]; group
    · rintro _ ⟨g, rfl⟩ h1
      have h2 : x' = 1 := by
        calc x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have h3 : x = 1 := congrArg Subtype.val h2
      exact h.x_ne_one h3
    · rintro ⟨g, hg⟩
      have hgc : (g : G) * x * (g : G)⁻¹ = L4.vElt x a := congrArg Subtype.val hg
      exact not_isConj_x_v5 h L.hT32 (isConj_iff.2 ⟨g, hgc⟩)
    · rintro _ ⟨g', rfl⟩ g
      exact ⟨g * g', by group⟩
    · show IsSylowOf 2 (S.subgroupOf Cv) ⊤
      rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
        Subgroup.range_subtype, inf_eq_left.2 hSCv]
      exact h.sylowS.of_le hSCv le_top
    · exact fun e he => hTS (hEgT he)
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgCv).toEquiv).trans L.card_EG
    · exact fun a ha b hb => Subtype.ext (L.EG_comm a ha b hb)
    · exact fun a ha => Subtype.ext (L.EG_sq a ha)
    · exact L.v_mem_EG
    · exact fun s hs e he => L.S_norm_EG (s : G) hs (e : G) he
    ·
      intro y hy
      constructor
      · rintro ⟨g, hg⟩
        have hgy : (g : G) * x * (g : G)⁻¹ = (y : G) := congrArg Subtype.val hg
        have hxy : IsConj x (y : G) := isConj_iff.2 ⟨g, hgy⟩
        have hy2 : orderOf (y : G) = 2 := by rw [← hgy]; exact hconjord g
        have hyS : (y : G) ∈ S := hy
        have hyc : (y : G) * L4.vElt x a = L4.vElt x a * (y : G) :=
          mem_centralizer_singleton_iff.1 y.2
        have hy3 : (y : G) * L4.vElt x a ∈
            ({z : G | ∃ g' : ↥Cv, (g' : G) * x * (g' : G)⁻¹ = z}) := by
          obtain ⟨g'', hg''⟩ := hZmv y ⟨g, hg⟩
          exact ⟨g'', congrArg Subtype.val hg''⟩
        have hy1G : (y : G) * (y : G) = 1 := by
          have h5 := pow_orderOf_eq_one (y : G)
          rw [hy2, sq] at h5
          exact h5
        have hyne : (y : G) ≠ 1 := by
          intro h6
          rw [h6, orderOf_one] at hy2
          omega
        have hyord : orderOf (⟨(y : G), hyS⟩ : ↥S) = 2 :=
          L4.orderOf_eq_two_of_mul_self _ hy1G hyne
        have hxord : orderOf (⟨x, L.hxS⟩ : ↥S) = 2 :=
          L4.orderOf_eq_two_of_mul_self _ (L4.x_mul_self h) h.x_ne_one
        have hnm4 : numMoved (L.ψ ⟨(y : G), hyS⟩) = 4 := by
          have h7 := (L.hψ.conj ⟨(y : G), hyS⟩ ⟨x, L.hxS⟩ hyord hxord).1 hxy.symm
          rw [L.hψ.x_eq] at h7
          exact h7.trans nmE_f1
        have hψsq : L.ψ ⟨(y : G), hyS⟩ * L.ψ ⟨(y : G), hyS⟩ = 1 := by
          rw [← map_mul]
          have : (⟨(y : G), hyS⟩ : ↥S) * ⟨(y : G), hyS⟩ = 1 := Subtype.ext hy1G
          rw [this, map_one]
        have hψne : L.ψ ⟨(y : G), hyS⟩ ≠ 1 := fun h7 =>
          hyne (congrArg Subtype.val (L.hψ.inj (h7.trans (map_one _).symm)))
        have hyT : (y : G) ∈ T := by
          by_contra hnT
          have hψR : L.ψ ⟨(y : G), hyS⟩ ∉ R5 := fun hm =>
            hnT ((psi_mem_R5_iff h L.hψ ⟨(y : G), hyS⟩).2 hm)
          have h8 := S0_inv_nm8 (L.hψ.mem ⟨(y : G), hyS⟩) hψsq hψne hψR
          rw [h8] at hnm4
          omega
        have hxyv : IsConj x ((y : G) * L4.vElt x a) := by
          obtain ⟨g', hg'⟩ := hy3
          exact isConj_iff.2 ⟨g', hg'⟩
        have hyvS : (y : G) * L4.vElt x a ∈ S := mul_mem hyS L.hvS
        have hyvsq : (y : G) * L4.vElt x a * ((y : G) * L4.vElt x a) = 1 := by
          calc (y : G) * L4.vElt x a * ((y : G) * L4.vElt x a)
              = (y : G) * (L4.vElt x a * (y : G)) * L4.vElt x a := by group
            _ = (y : G) * ((y : G) * L4.vElt x a) * L4.vElt x a := by rw [← hyc]
            _ = ((y : G) * (y : G)) * (L4.vElt x a * L4.vElt x a) := by group
            _ = 1 := by rw [hy1G, L4.v_mul_self h, one_mul]
        have hyvne : (y : G) * L4.vElt x a ≠ 1 := by
          intro h1
          have h2 : (y : G) = (L4.vElt x a)⁻¹ := by
            calc (y : G) = (y : G) * L4.vElt x a * (L4.vElt x a)⁻¹ := by group
              _ = (L4.vElt x a)⁻¹ := by rw [h1, one_mul]
          have h3 : (L4.vElt x a)⁻¹ = L4.vElt x a := inv_eq_of_mul_eq_one_right (L4.v_mul_self h)
          rw [h3] at h2
          rw [h2] at hxy
          exact not_isConj_x_v5 h L.hT32 hxy
        have hyvord : orderOf (⟨(y : G) * L4.vElt x a, hyvS⟩ : ↥S) = 2 :=
          L4.orderOf_eq_two_of_mul_self _ hyvsq hyvne
        have hψyv : L.ψ ⟨(y : G) * L4.vElt x a, hyvS⟩ = L.ψ ⟨(y : G), hyS⟩ * yS := by
          have h9 : (⟨(y : G) * L4.vElt x a, hyvS⟩ : ↥S) = ⟨(y : G), hyS⟩ * ⟨L4.vElt x a, L.hvS⟩ :=
            rfl
          rw [h9, map_mul, L.hψ.v_eq]
        have hnm4' : numMoved (L.ψ ⟨(y : G), hyS⟩ * yS) = 4 := by
          have h7 := (L.hψ.conj ⟨(y : G) * L4.vElt x a, hyvS⟩ ⟨x, L.hxS⟩ hyvord hxord).1
            hxyv.symm
          rw [L.hψ.x_eq, hψyv] at h7
          exact h7.trans nmE_f1
        have hchar := (E9_char (L.hψ.mem ⟨(y : G), hyS⟩) hψsq hψne).2 ⟨hnm4, hnm4'⟩
        refine ⟨L.mem_EG.2 ⟨hyS, hchar.1⟩, ?_, ?_⟩
        · intro h7
          exact hyne (congrArg Subtype.val h7)
        · intro h7
          have h8 : (y : G) = L4.vElt x a := congrArg Subtype.val h7
          have h9 : (⟨(y : G), hyS⟩ : ↥S) = ⟨L4.vElt x a, L.hvS⟩ := Subtype.ext h8
          rw [h9, L.hψ.v_eq] at hchar
          exact hchar.2 rfl
      · rintro ⟨hyE, hy1, hyv⟩
        obtain ⟨g, hg, hgy⟩ := L.EG_class5 hyE (fun h' => hy1 (Subtype.ext h'))
          (fun h' => hyv (Subtype.ext h'))
        exact ⟨⟨g, (hmemCv g).2 hg⟩, Subtype.ext hgy⟩
    · exact ⟨1, by simp⟩
    · exact L.x_mem_EG
    · exact fun z hz => hz
    · intro g hg e he
      have hgx : (g : G) * x = x * (g : G) := congrArg Subtype.val hg
      have hgv : (g : G) * L4.vElt x a = L4.vElt x a * (g : G) :=
        mem_centralizer_singleton_iff.1 g.2
      exact L.D_norm5 hgx hgv he
  have hS : Nat.card S' ≤ 128 := by
    have : Nat.card S' = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSCv).toEquiv
    rw [this, L.card_S]
    norm_num
  have hex : ∃ s ∈ S', s * s = 1 ∧ s ∉ E' := by
    obtain ⟨s, hs⟩ := L.hψ.surj (a0perm 5) a0_mem_S0
    have hss : s * s = 1 := L.hψ.inj (by rw [map_mul, hs, a0_sq, map_one])
    have hssG := congrArg Subtype.val hss
    refine ⟨⟨(s : G), hSCv s.2⟩, s.2, Subtype.ext hssG, ?_⟩
    intro hmem
    obtain ⟨hyS, hψE⟩ := L.mem_EG.1 hmem
    have h7 : L.ψ ⟨(s : G), hyS⟩ = a0perm 5 := hs
    have hψE' : L.ψ ⟨(s : G), hyS⟩ ∈ E9 := hψE
    rw [h7] at hψE'
    exact a0_notin_R5 (E9_le_R5 hψE')
  have hZS : ∀ s ∈ S', (∀ t ∈ S', s * t = t * s) → s * s = 1 → s ≠ 1 → s = v' := by
    intro s hs hcen hs2 hs1
    have hsS : (s : G) ∈ S := hs
    have hψc : ∀ t ∈ S0, L.ψ ⟨(s : G), hsS⟩ * t = t * L.ψ ⟨(s : G), hsS⟩ := by
      intro t ht
      obtain ⟨t', rfl⟩ := L.hψ.surj t ht
      have h1 : s * (⟨(t' : G), hSCv t'.2⟩ : ↥Cv) = ⟨(t' : G), hSCv t'.2⟩ * s :=
        hcen _ t'.2
      have h2 := congrArg Subtype.val h1
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h2
    rcases Z_S0 (L.hψ.mem ⟨(s : G), hsS⟩) hψc with h1 | h1
    · exfalso
      apply hs1
      have h3 : (⟨(s : G), hsS⟩ : ↥S) = 1 := L.hψ.inj (h1.trans (map_one _).symm)
      have h4 := congrArg Subtype.val h3
      exact Subtype.ext h4
    · have h3 : (⟨(s : G), hsS⟩ : ↥S) = ⟨L4.vElt x a, L.hvS⟩ :=
        L.hψ.inj (h1.trans L.hψ.v_eq.symm)
      have h4 := congrArg Subtype.val h3
      exact Subtype.ext h4
  have hNT := L4.normalizer_eq_top hZD hTI hS hex hZS
  intro g hg e he
  have hgC : g ∈ Cv := (hmemCv g).2 hg
  have hmem : (⟨g, hgC⟩ : ↥Cv) ∈ normalizer (E' : Set ↥Cv) := by
    rw [hNT]
    exact mem_top _
  exact (mem_normalizer_iff.1 hmem ⟨e, hEgCv he⟩).1 he

theorem exists_lam :
    ∃ lam : ↥(L.EG.subgroupOf (centralizer ({L4.vElt x a} : Set G))) ≃*
        ↥(E9A.subgroupOf C2),
      ∀ e : ↥(L.EG.subgroupOf (centralizer ({L4.vElt x a} : Set G))),
        ((((lam e : ↥(E9A.subgroupOf C2)) : ↥C2) : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
          L.ψ ⟨(((e : ↥(centralizer ({L4.vElt x a} : Set G))) : G)),
            L.EG_le_S (L.mem_EG_of_sub e)⟩ := by
  have hTS : T ≤ S := h.T_lt_S.le
  set Cv : Subgroup G := centralizer ({L4.vElt x a} : Set G) with hCv
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * L4.vElt x a = L4.vElt x a * g := fun g =>
    mem_centralizer_singleton_iff
  have hEgCv : L.EG ≤ Cv := L.EG_le_T.trans (L4.T_le_centralizer_v h)
  let f : ↥(L.EG.subgroupOf Cv) →* Perm (Fin 9) :=
    L.ψ.comp ((Subgroup.inclusion L.EG_le_S).comp (Subgroup.subgroupOfEquivOfLe hEgCv).toMonoidHom)
  have hf : ∀ e : ↥(L.EG.subgroupOf Cv),
      f e = L.ψ ⟨((e : ↥Cv) : G), L.EG_le_S (L.mem_EG_of_sub e)⟩ := fun e => rfl
  have hfE : ∀ e : ↥(L.EG.subgroupOf Cv), f e ∈ E9 := by
    intro e
    rw [hf]
    exact (L.mem_EG.1 (L.mem_EG_of_sub e)).2
  let θ₀ : ↥(L.EG.subgroupOf Cv) →* ↥(alternatingGroup (Fin 9)) :=
    f.codRestrict (alternatingGroup (Fin 9)) (fun e => E9_le_alt (hfE e))
  let θ₁ : ↥(L.EG.subgroupOf Cv) →* ↥C2 :=
    θ₀.codRestrict C2 (fun e => mem_C2.2 (E9_comm _ (hfE e) _ yS_mem_E9))
  let θ : ↥(L.EG.subgroupOf Cv) →* ↥(E9A.subgroupOf C2) :=
    θ₁.codRestrict (E9A.subgroupOf C2) (fun e => mem_E2.2 (mem_E9l.2 (hfE e)))
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : f e = 1 := by
      have h2 := congrArg (fun z : ↥(E9A.subgroupOf C2) =>
        (((z : ↥C2) : alternatingGroup (Fin 9)) : Perm (Fin 9))) he
      exact h2
    have h3 : (⟨((e : ↥Cv) : G), L.EG_le_S (L.mem_EG_of_sub e)⟩ : ↥S) = 1 :=
      L.hψ.inj ((hf e).symm.trans (h1.trans (map_one _).symm))
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext (Subtype.ext h4)
  have hE' : Nat.card (L.EG.subgroupOf Cv) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgCv).toEquiv).trans L.card_EG
  have hθbij : Function.Bijective θ :=
    hθinj.bijective_of_nat_card_le (by rw [card_E2, hE'])
  exact ⟨MulEquiv.ofBijective θ hθbij, fun e => rfl⟩

theorem exists_equiv_centralizer_v5
    (hZD : CFSG.GH74.Uniqueness.S_ZD) :
    ∃ v' : alternatingGroup (Fin 9), orderOf v' = 2 ∧ numMoved (v' : Perm (Fin 9)) = 8 ∧
      Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
        ↥(centralizer ({v'} : Set (alternatingGroup (Fin 9))))) := by
  refine ⟨vA, ?_, numMoved_yS, ?_⟩
  · exact orderOf_eq_prime (by rw [sq]; exact Subtype.ext yS_sq)
      (fun h1 => yS_ne_one (congrArg Subtype.val h1))
  have hnorm := L.normalizer_EG5 hZD
  obtain ⟨D₂, hcompl₂, hnorm₂, hc₂, hE₂, hsq₂, hcent₂⟩ := star9_data
  have hTS : T ≤ S := h.T_lt_S.le
  set Cv : Subgroup G := centralizer ({L4.vElt x a} : Set G) with hCv
  obtain ⟨lam, hlam⟩ := L.exists_lam
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * L4.vElt x a = L4.vElt x a * g := fun g =>
    mem_centralizer_singleton_iff
  have hTCv : T ≤ Cv := L4.T_le_centralizer_v h
  have hSCv : S ≤ Cv := by
    intro s hs
    rw [hmemCv]
    have h1 := congrArg Subtype.val (L.hψ.v_cent ⟨s, hs⟩)
    exact h1
  have hEgCv : L.EG ≤ Cv := L.EG_le_T.trans hTCv
  have hRSCv : L.RS ≤ Cv := L.RS_le_S.trans hSCv
  let v' : ↥Cv := ⟨L4.vElt x a, (hmemCv _).2 rfl⟩
  let x' : ↥Cv := ⟨x, L4.x_mem_centralizer_v h⟩
  let E' : Subgroup ↥Cv := L.EG.subgroupOf Cv
  let R' : Subgroup ↥Cv := L.RS.subgroupOf Cv
  have hv'c : ∀ g : ↥Cv, g * v' = v' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hSyl : IsSylowOf 2 (S.subgroupOf Cv) ⊤ := by
    rw [← isSylowOf_map_subtype_iff Cv, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype, inf_eq_left.2 hSCv]
    exact h.sylowS.of_le hSCv le_top
  obtain ⟨P, hP⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hSyl
  have hv1 : v' ≠ 1 := fun h1 => L4.v_ne_one h (congrArg Subtype.val h1)
  have hEn : E'.Normal :=
    ⟨fun e he g => hnorm (g : G) (mem_centralizer_singleton_iff.1 g.2) (e : G) he⟩
  have hEcard : Nat.card E' = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEgCv).toEquiv).trans L.card_EG
  have hEcomm : ∀ a ∈ E', ∀ a' ∈ E', a * a' = a' * a := fun a ha b hb =>
    Subtype.ext (L.EG_comm a ha b hb)
  have hvE : v' ∈ E' := L.v_mem_EG
  have hxE : x' ∈ E' := L.x_mem_EG
  have hx1 : x' ≠ 1 := fun h1 => h.x_ne_one (congrArg Subtype.val h1)
  have hxv : x' ≠ v' := by
    intro h1
    have h3 : x = L4.vElt x a := congrArg Subtype.val h1
    apply not_isConj_x_v5 h L.hT32
    rw [show x * (a * x * a⁻¹) = x from h3.symm]
  have hcls : ∀ e ∈ E', e ≠ 1 → e ≠ v' → ∃ g : ↥Cv, g * x' * g⁻¹ = e := by
    intro e he he1 hev
    obtain ⟨g, hg, hgy⟩ := L.EG_class5 (y := (e : G)) he (fun h' => he1 (Subtype.ext h'))
      (fun h' => hev (Subtype.ext h'))
    exact ⟨⟨g, (hmemCv g).2 hg⟩, Subtype.ext hgy⟩
  have hD : Nat.card ↥(centralizer ({x'} : Set ↥Cv)) = 32 := by
    have hcen : centralizer ({x'} : Set ↥Cv) = T.subgroupOf Cv := by
      ext g
      constructor
      · intro hg
        have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hg)
        have hgv : (g : G) * L4.vElt x a = L4.vElt x a * (g : G) :=
          mem_centralizer_singleton_iff.1 g.2
        exact L.cent_xv_T h1 hgv
      · intro hg
        have hgT : (g : G) ∈ T := hg
        have hgx : (g : G) * x = x * (g : G) := mem_centralizer_singleton_iff.1 (h.T_le_C hgT)
        exact mem_centralizer_singleton_iff.2 (Subtype.ext hgx)
    rw [hcen]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTCv).toEquiv).trans L.hT32
  have hcent : ∀ c : ↥Cv, (∀ e ∈ E', c * e = e * c) → c ∈ E' := by
    intro c hc
    have hgx : (c : G) * x = x * (c : G) := by
      have h1 := congrArg Subtype.val (hc x' hxE)
      exact h1
    have hgv : (c : G) * L4.vElt x a = L4.vElt x a * (c : G) := mem_centralizer_singleton_iff.1 c.2
    have hcT : (c : G) ∈ T := L.cent_xv_T hgx hgv
    let cT : ↥T := ⟨(c : G), hcT⟩
    have hcE5 : L.pc cT ∈ E5 := by
      apply centT_E5 (L.pc_mem cT)
      intro p hp
      obtain ⟨tp, htp⟩ := L.exists_pc (E5_le_T5 hp)
      have htpE : (tp : G) ∈ L.EG := (L.mem_EG_T tp).2 (by rw [htp]; exact hp)
      have h1 : cT * tp = tp * cT := by
        have h2 := hc ⟨(tp : G), hEgCv htpE⟩ htpE
        have h3 := congrArg Subtype.val h2
        exact Subtype.ext h3
      have h4 := congrArg L.pc h1
      rw [L.pc_mul, L.pc_mul, htp] at h4
      exact h4
    exact (L.mem_EG_T cT).2 hcE5
  have hEP : E' ≤ (P : Subgroup ↥Cv) := by
    rw [hP]
    exact fun e he => L.EG_le_S he
  have hER : E' ⊓ R' = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he1, he2⟩
    have h1 : (e : G) ∈ L.EG ⊓ L.RS := ⟨he1, he2⟩
    rw [L.EG_inf_RS, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hERP : E' ⊔ R' = (P : Subgroup ↥Cv) := by
    have h1 : E' ⊔ R' = (L.EG ⊔ L.RS).subgroupOf Cv :=
      (Subgroup.subgroupOf_sup hEgCv hRSCv).symm
    rw [h1, L.EG_sup_RS, hP]
  let vC : ↥C2 := ⟨vA, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hvC : vC ∈ E9A.subgroupOf C2 := mem_E2.2 (mem_E9l.2 yS_mem_E9)
  have hvC1 : vC ≠ 1 := fun h1 => yS_ne_one (congrArg (fun z : ↥C2 =>
    (((z : ↥C2) : alternatingGroup (Fin 9)) : Perm (Fin 9))) h1)
  have hvcC : ∀ c : ↥C2, c * vC = vC * c := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  have hlam' : lam ⟨v', hvE⟩ = ⟨vC, hvC⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (hlam ⟨v', hvE⟩).trans L.hψ.v_eq
  exact exists_mulEquiv_five_of_data v' x' E' P R' (E9A.subgroupOf C2) D₂ hv1 hv'c hEn hEcard hEcomm
    hvE hxE hx1 hxv hcls hD hcent hEP hER hERP hnorm₂ hcompl₂ hc₂ hE₂ hsq₂ vC hvC hvC1 hvcC
    hcent₂ lam hlam'

end Loc5

end CFSG.GH74.GLS.C3.Layer2.L5
