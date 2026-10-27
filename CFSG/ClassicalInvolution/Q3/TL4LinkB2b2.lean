module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b1
public import CFSG.ClassicalInvolution.Q3.Q3CHS2Tri
public import CFSG.ClassicalInvolution.AschTight.S1916Help

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure SylowTri (Ω : Set (Subgroup G)) (S : Sylow 2 G) (K J M P T T' : Subgroup G)
    (t u : G) : Prop where
  mem_K : K ∈ Ω
  mem_J : J ∈ Ω
  mem_M : M ∈ Ω
  inv_K : IsUniqueInvolution K t
  inv_J : IsUniqueInvolution J u
  inv_M : IsUniqueInvolution M (t * u)
  syl_P : IsSylow2In P K
  syl_T : IsSylow2In T J
  syl_T' : IsSylow2In T' M
  le_P : P ≤ (S : Subgroup G)
  le_T : T ≤ (S : Subgroup G)
  le_T' : T' ≤ (S : Subgroup G)
  comm_PT : Commutes P T
  comm_PT' : Commutes P T'
  comm_TT' : Commutes T T'
  rset : ∀ A ∈ RSet Ω, A ≤ (S : Subgroup G) → A = P ∨ A = T ∨ A = T'

namespace SylowTri

variable {S : Sylow 2 G} {K J M P T T' : Subgroup G} {t u : G}

private theorem t_mem (h : SylowTri Ω S K J M P T T' t u) : t ∈ P :=
  Sec6Gen.mem_of_isSylow2In h.inv_K h.syl_P

private theorem u_mem (h : SylowTri Ω S K J M P T T' t u) : u ∈ T :=
  Sec6Gen.mem_of_isSylow2In h.inv_J h.syl_T

private theorem mul_comm_tu (h : SylowTri Ω S K J M P T T' t u) : t * u = u * t :=
  h.comm_PT t h.t_mem u h.u_mem

theorem rot (h : SylowTri Ω S K J M P T T' t u) : SylowTri Ω S J M K T T' P u (t * u) := by
  have htu : u * (t * u) = t := by rw [h.mul_comm_tu, ← mul_assoc, h.inv_J.sq, one_mul]
  exact
    { mem_K := h.mem_J
      mem_J := h.mem_M
      mem_M := h.mem_K
      inv_K := h.inv_J
      inv_J := h.inv_M
      inv_M := by rw [htu]; exact h.inv_K
      syl_P := h.syl_T
      syl_T := h.syl_T'
      syl_T' := h.syl_P
      le_P := h.le_T
      le_T := h.le_T'
      le_T' := h.le_P
      comm_PT := h.comm_TT'
      comm_PT' := h.comm_PT.symm
      comm_TT' := h.comm_PT'.symm
      rset := fun A hA hAS => by
        rcases h.rset A hA hAS with h1 | h1 | h1
        · exact Or.inr (Or.inr h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1) }

theorem conj (hΩ : ConjInvariant Ω) (h : SylowTri Ω S K J M P T T' t u) (g : G) :
    SylowTri Ω (g • S) (conjSub g K) (conjSub g J) (conjSub g M) (conjSub g P) (conjSub g T)
      (conjSub g T') (g * t * g⁻¹) (g * u * g⁻¹) := by
  have hS : ((g • S : Sylow 2 G) : Subgroup G) = conjSub g (S : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    ext x
    simp [conjSub, Subgroup.pointwise_smul_def]
  have htu : g * t * g⁻¹ * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
  refine
    { mem_K := hΩ g K h.mem_K
      mem_J := hΩ g J h.mem_J
      mem_M := hΩ g M h.mem_M
      inv_K := h.inv_K.conj g
      inv_J := h.inv_J.conj g
      inv_M := by rw [htu]; exact h.inv_M.conj g
      syl_P := h.syl_P.conj g
      syl_T := h.syl_T.conj g
      syl_T' := h.syl_T'.conj g
      le_P := hS ▸ conjSub_mono h.le_P
      le_T := hS ▸ conjSub_mono h.le_T
      le_T' := hS ▸ conjSub_mono h.le_T'
      comm_PT := h.comm_PT.conjSub g
      comm_PT' := h.comm_PT'.conjSub g
      comm_TT' := h.comm_TT'.conjSub g
      rset := fun A hA hAS => ?_ }
  have hAS' : conjSub g⁻¹ A ≤ (S : Subgroup G) := by
    rw [hS] at hAS
    have := conjSub_mono (n := g⁻¹) hAS
    rwa [conjSub_inv_conjSub] at this
  have e : A = conjSub g (conjSub g⁻¹ A) := (conjSub_conjSub_inv g A).symm
  rcases h.rset _ (RSet.conj hΩ hA g⁻¹) hAS' with h1 | h1 | h1
  · exact Or.inl (by rw [e, h1])
  · exact Or.inr (Or.inl (by rw [e, h1]))
  · exact Or.inr (Or.inr (by rw [e, h1]))

theorem adj (hΩ : TypeRFam r Ω) (h : SylowTri Ω S K J M P T T' t u) :
    J ∈ omegaNbr Ω K ∧ M ∈ omegaNbr Ω K ∧ M ∈ omegaNbr Ω J := by
  have hTt : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_PT t h.t_mem x hx).symm
  have hT't : T' ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_PT' t h.t_mem x hx).symm
  have hT'u : T' ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_TT' u h.u_mem x hx).symm
  have hNK := hΩ.tight K h.mem_K t h.inv_K
  have hNJ := hΩ.tight J h.mem_J u h.inv_J
  refine ⟨⟨h.mem_J, ?_, T, mem_RSet_of_isSylow2In h.mem_J h.syl_T, h.syl_T.1, hTt.trans hNK⟩,
    ⟨h.mem_M, ?_, T', mem_RSet_of_isSylow2In h.mem_M h.syl_T', h.syl_T'.1, hT't.trans hNK⟩,
    ⟨h.mem_M, ?_, T', mem_RSet_of_isSylow2In h.mem_M h.syl_T', h.syl_T'.1, hT'u.trans hNJ⟩⟩
  · intro hJK
    have h1 : t = u := h.inv_K.eq (hJK ▸ h.inv_J)
    apply h.inv_M.ne_one
    rw [h1, h.inv_J.sq]
  · intro hMK
    have h1 : t = t * u := h.inv_K.eq (hMK ▸ h.inv_M)
    apply h.inv_J.ne_one
    calc u = t⁻¹ * (t * u) := by group
      _ = 1 := by rw [← h1, inv_mul_cancel]
  · intro hMJ
    have h1 : u = t * u := h.inv_J.eq (hMJ ▸ h.inv_M)
    apply h.inv_K.ne_one
    calc t = t * u * u⁻¹ := by group
      _ = 1 := by rw [← h1, mul_inv_cancel]

theorem perm_inv (hΩ : ConjInvariant Ω) (h : SylowTri Ω S K J M P T T' t u) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    s * t * s⁻¹ ∈ ({t, u, t * u} : Set G) ∧ s * u * s⁻¹ ∈ ({t, u, t * u} : Set G) := by
  have key : ∀ {A : Subgroup G} {x : G}, A ∈ RSet Ω → A ≤ (S : Subgroup G) → x ∈ A →
      x * x = 1 → x ≠ 1 → x ∈ ({t, u, t * u} : Set G) := by
    intro A x hA hAS hxA hx2 hx1
    rcases h.rset A hA hAS with rfl | rfl | rfl
    · exact Or.inl ((h.inv_K.unique x (h.syl_P.1 hxA) hx2).resolve_left hx1)
    · exact Or.inr (Or.inl ((h.inv_J.unique x (h.syl_T.1 hxA) hx2).resolve_left hx1))
    · exact Or.inr (Or.inr ((h.inv_M.unique x (h.syl_T'.1 hxA) hx2).resolve_left hx1))
  have hsq : ∀ x : G, x * x = 1 → s * x * s⁻¹ * (s * x * s⁻¹) = 1 := by
    intro x hx
    calc s * x * s⁻¹ * (s * x * s⁻¹) = s * (x * x) * s⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hne : ∀ x : G, x ≠ 1 → s * x * s⁻¹ ≠ 1 := by
    intro x hx h1
    apply hx
    calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = 1 := by rw [h1]; group
  exact ⟨key (RSet.conj hΩ (mem_RSet_of_isSylow2In h.mem_K h.syl_P) s)
      (conjSub_le_of_le_of_mem_left h.le_P hs) (conj_mem_conjSub h.t_mem) (hsq t h.inv_K.sq)
      (hne t h.inv_K.ne_one),
    key (RSet.conj hΩ (mem_RSet_of_isSylow2In h.mem_J h.syl_T) s)
      (conjSub_le_of_le_of_mem_left h.le_T hs) (conj_mem_conjSub h.u_mem) (hsq u h.inv_J.sq)
      (hne u h.inv_J.ne_one)⟩

theorem eq_of_sylow (hΩ : HypOmegaGen Ω) (h : SylowTri Ω S K J M P T T' t u) {L A : Subgroup G}
    (hL : L ∈ Ω) (hA : IsSylow2In A L) (hAS : A ≤ (S : Subgroup G)) :
    L = K ∨ L = J ∨ L = M := by
  have hAR := mem_RSet_of_isSylow2In hL hA
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hAR
  rcases h.rset A hAR hAS with rfl | rfl | rfl
  · exact Or.inl (Sec6Gen.eq_of_le_of_le hΩ hL h.mem_K hA.2.1 (by omega) hA.1 h.syl_P.1)
  · exact Or.inr (Or.inl
      (Sec6Gen.eq_of_le_of_le hΩ hL h.mem_J hA.2.1 (by omega) hA.1 h.syl_T.1))
  · exact Or.inr (Or.inr
      (Sec6Gen.eq_of_le_of_le hΩ hL h.mem_M hA.2.1 (by omega) hA.1 h.syl_T'.1))

end SylowTri

private theorem conjSub_layerY_of_mem_centralizer (hΩ : ConjInvariant Ω) {x c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : conjSub c (layerY Ω x) = layerY Ω x := by
  have key : ∀ d ∈ Subgroup.centralizer ({x} : Set G),
      conjSub d (layerY Ω x) ≤ layerY Ω x := by
    intro d hd
    unfold layerY
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_layerY (conjSub_mem_coreFam hΩ hC hd)
  refine le_antisymm (key c hc) ?_
  have h := conjSub_mono (n := c) (key c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hc))
  rwa [conjSub_conjSub_inv] at h

private theorem conjSub_layerQ_of_mem_centralizer (hΩ : ConjInvariant Ω) {x c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : conjSub c (layerQ Ω x) = layerQ Ω x := by
  unfold layerQ
  rw [← Thompson.oddCoreOf_conjSub_eq, conjSub_layerY_of_mem_centralizer hΩ hc]

private theorem conj_eq_of_mem_layerQ (hΩ : ConjInvariant Ω) {x ν w : G} {S : Subgroup G}
    (hS : IsPGroup 2 S) (hν : ν ∈ layerQ Ω x) (hwS : w ∈ S)
    (hwx : w ∈ Subgroup.centralizer ({x} : Set G)) (hνw : ν * w * ν⁻¹ ∈ S) :
    ν * w * ν⁻¹ = w := by
  have h1 : w * ν⁻¹ * w⁻¹ ∈ layerQ Ω x := by
    rw [← conjSub_layerQ_of_mem_centralizer hΩ hwx]
    exact conj_mem_conjSub ((layerQ Ω x).inv_mem hν)
  have hc : ν * w * ν⁻¹ * w⁻¹ ∈ layerQ Ω x := by
    have := (layerQ Ω x).mul_mem hν h1
    rwa [show ν * (w * ν⁻¹ * w⁻¹) = ν * w * ν⁻¹ * w⁻¹ by group] at this
  have hcS : ν * w * ν⁻¹ * w⁻¹ ∈ S := S.mul_mem hνw (S.inv_mem hwS)
  have h2 : ν * w * ν⁻¹ * w⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (layerY Ω x)) hc
      (hS.to_le (Subgroup.zpowers_le.mpr hcS))
  calc ν * w * ν⁻¹ = ν * w * ν⁻¹ * w⁻¹ * w := by group
    _ = w := by rw [h2, one_mul]

namespace Tri

variable {K J M : Subgroup G} {t u : G}

theorem exists_commuting_sylows (h : Tri r Ω K J M t u) :
    ∃ P T T' : Subgroup G, IsSylow2In P K ∧ IsSylow2In T J ∧ IsSylow2In T' M ∧
      Commutes P T ∧ Commutes P T' ∧ Commutes T T' := by
  have hΩ := h.fam.hyp
  have hJΩ := h.adj_J.1
  have hMΩ := h.adj_M.1
  obtain ⟨-, -, T, hTR, hTJ, hTN⟩ := h.adj_J
  have hT : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTR hTJ
  obtain ⟨P, hP, hPfix⟩ := AscL62.exists_sylow_normalized hT.2.1 hTN
  have hPR := mem_RSet_of_isSylow2In h.mem hP
  have htP : t ∈ P := Sec6Gen.mem_of_isSylow2In h.inv_K hP
  have huT : u ∈ T := Sec6Gen.mem_of_isSylow2In h.inv_J hT
  have hTP2 : IsPGroup 2 ↥(T ⊔ P) := hT.2.1.to_sup_of_normal_right' hP.2.1
    (fun w hw => mem_normalizer_iff_conjSub_eq.mpr (hPfix w hw))
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hTP2
  have hPT : Commutes P T := Q3CP.l67Gen G Ω hΩ S₀ P hPR T hTR (le_sup_right.trans hS₀)
    (le_sup_left.trans hS₀) fun hPT => h.ne_tu
      ((h.inv_J.unique t (hTJ (hPT ▸ htP)) h.inv_K.sq).resolve_left h.inv_K.ne_one)
  have hPt : P ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution h.inv_K
      (Subgroup.le_normalizer (hP.1 hx))
  have hPu : P ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPT x hx u huT)
  have hTt : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hPT t htP x hx).symm
  have hTu : T ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution h.inv_J
      (Subgroup.le_normalizer (hT.1 hx))
  have key : ∀ x, x ∈ Subgroup.centralizer ({t} : Set G) →
      x ∈ Subgroup.centralizer ({u} : Set G) → x ∈ Subgroup.centralizer ({t * u} : Set G) := by
    intro x h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 h2 ⊢
    calc x * (t * u) = x * t * u := by group
      _ = t * x * u := by rw [h1]
      _ = t * (x * u) := by group
      _ = t * (u * x) := by rw [h2]
      _ = t * u * x := by group
  have hXtu : P ⊔ T ≤ Subgroup.centralizer ({t * u} : Set G) :=
    sup_le (fun x hx => key x (hPt hx) (hPu hx)) (fun x hx => key x (hTt hx) (hTu hx))
  have hX2 : IsPGroup 2 ↥(P ⊔ T) := Q3CH.isPGroup_sup_of_commute hP.2.1 hT.2.1 hPT
  obtain ⟨T', hT', hT'fix⟩ := AscL62.exists_sylow_normalized hX2
    (hXtu.trans (h.fam.tight M hMΩ (t * u) h.inv_M))
  have hY2 : IsPGroup 2 ↥((P ⊔ T) ⊔ T') := hX2.to_sup_of_normal_right' hT'.2.1
    (fun w hw => mem_normalizer_iff_conjSub_eq.mpr (hT'fix w hw))
  obtain ⟨S₁, hS₁⟩ := IsPGroup.exists_le_sylow hY2
  have hPS₁ : P ≤ (S₁ : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS₁)
  have hTS₁ : T ≤ (S₁ : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS₁)
  have hT'S₁ : T' ≤ (S₁ : Subgroup G) := le_sup_right.trans hS₁
  have hT'R := mem_RSet_of_isSylow2In hMΩ hT'
  refine ⟨P, T, T', hP, hT, hT', hPT, Q3CP.l67Gen G Ω hΩ S₁ P hPR T' hT'R hPS₁ hT'S₁ ?_,
    Q3CP.l67Gen G Ω hΩ S₁ T hTR T' hT'R hTS₁ hT'S₁ ?_⟩
  · intro hPT'
    have h1 : t = t * u :=
      (h.inv_M.unique t (hT'.1 (hPT' ▸ htP)) h.inv_K.sq).resolve_left h.inv_K.ne_one
    apply h.inv_J.ne_one
    calc u = t⁻¹ * (t * u) := by group
      _ = 1 := by rw [← h1, inv_mul_cancel]
  · intro hTT'
    have h1 : u = t * u :=
      (h.inv_M.unique u (hT'.1 (hTT' ▸ huT)) h.inv_J.sq).resolve_left h.inv_J.ne_one
    apply h.inv_K.ne_one
    calc t = t * u * u⁻¹ := by group
      _ = 1 := by rw [← h1, mul_inv_cancel]

theorem sylowTri_of_commuting (h : Tri r Ω K J M t u) {S : Sylow 2 G} {P T T' : Subgroup G}
    (hP : IsSylow2In P K) (hT : IsSylow2In T J) (hT' : IsSylow2In T' M)
    (hPS : P ≤ (S : Subgroup G)) (hTS : T ≤ (S : Subgroup G)) (hT'S : T' ≤ (S : Subgroup G))
    (hPT : Commutes P T) (hPT' : Commutes P T') (hTT' : Commutes T T') :
    SylowTri Ω S K J M P T T' t u := by
  refine ⟨h.mem, h.adj_J.1, h.adj_M.1, h.inv_K, h.inv_J, h.inv_M, hP, hT, hT', hPS, hTS, hT'S,
    hPT, hPT', hTT', fun A hA hAS => ?_⟩
  have hΩ := h.fam.hyp
  have htP : t ∈ P := Sec6Gen.mem_of_isSylow2In h.inv_K hP
  have huT : u ∈ T := Sec6Gen.mem_of_isSylow2In h.inv_J hT
  have htuT' : t * u ∈ T' := Sec6Gen.mem_of_isSylow2In h.inv_M hT'
  obtain ⟨L, hL, hAL⟩ := exists_isSylow2In_of_mem_RSet hA
  have uniq : ∀ {B : Subgroup G}, IsSylow2In B L → B ≤ (S : Subgroup G) → A = B := by
    intro B hB hBS
    have hLS : IsPGroup 2 ↥(L ⊓ (S : Subgroup G)) := S.isPGroup'.to_le inf_le_right
    exact (hAL.2.2 _ inf_le_left hLS (le_inf hAL.1 hAS)).symm.trans
      (hB.2.2 _ inf_le_left hLS (le_inf hB.1 hBS))
  by_cases hAP : A = P
  · exact Or.inl hAP
  have hAc : Commutes P A :=
    Q3CP.l67Gen G Ω hΩ S P (mem_RSet_of_isSylow2In h.mem hP) A hA hPS hAS (Ne.symm hAP)
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc t htP x hx).symm
  by_cases hLK : L = K
  · subst hLK
    exact absurd (uniq hP hPS) hAP
  have hLnbr : L ∈ omegaNbr Ω K :=
    ⟨hL, hLK, A, hA, hAL.1, hAt.trans (h.fam.tight K h.mem t h.inv_K)⟩
  obtain ⟨ν, hν, hLν | hLν⟩ := h.h7 L hLnbr
  · have hzL : IsUniqueInvolution L (ν * u * ν⁻¹) := hLν ▸ h.inv_J.conj ν
    have hzA : ν * u * ν⁻¹ ∈ A := Sec6Gen.mem_of_isSylow2In hzL hAL
    have hut : u ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hPT t htP u huT).symm
    rw [conj_eq_of_mem_layerQ hΩ.conjInvariant S.isPGroup' hν (hTS huT) hut (hAS hzA)] at hzL
    have hLJ : L = J := h.fam.noTwins J h.adj_J.1 L ⟨hL, u, h.inv_J, hzL⟩
    subst hLJ
    exact Or.inr (Or.inl (uniq hT hTS))
  · have hzL : IsUniqueInvolution L (ν * (t * u) * ν⁻¹) := hLν ▸ h.inv_M.conj ν
    have hzA : ν * (t * u) * ν⁻¹ ∈ A := Sec6Gen.mem_of_isSylow2In hzL hAL
    have htut : t * u ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hPT' t htP (t * u) htuT').symm
    rw [conj_eq_of_mem_layerQ hΩ.conjInvariant S.isPGroup' hν (hT'S htuT') htut
      (hAS hzA)] at hzL
    have hLM : L = M := h.fam.noTwins M h.adj_M.1 L ⟨hL, t * u, h.inv_M, hzL⟩
    subst hLM
    exact Or.inr (Or.inr (uniq hT' hT'S))

theorem exists_std_sylowTri (h : Tri r Ω K J M t u) :
    ∃ (S : Sylow 2 G) (P T T' : Subgroup G), SylowTri Ω S K J M P T T' t u ∧
      IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
        (Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨P, T, T', hP, hT, hT', hPT, hPT', hTT'⟩ := h.exists_commuting_sylows
  have hΩ := h.fam.hyp
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hP.1 hP.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hP)
    omega)
  have hTT'2 : IsPGroup 2 ↥(T ⊔ T') := Q3CH.isPGroup_sup_of_commute hT.2.1 hT'.2.1 hTT'
  have hPc : T ⊔ T' ≤ Subgroup.centralizer (P : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun p hp => hPT p hp x hx)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun p hp => hPT' p hp x hx)
  have hP2 : IsPGroup 2 ↥(P ⊔ (T ⊔ T')) :=
    Q3CH.isPGroup_sup_of_commute hP.2.1 hTT'2 fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hPc hb) a ha
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hP2
  have hct : P ⊔ (T ⊔ T') ≤
      Subgroup.centralizer ((Subgroup.closure ({t} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure]
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro x hx
      exact S1916.normalizer_le_centralizer_of_isUniqueInvolution h.inv_K
        (Subgroup.le_normalizer (hP.1 hx))
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hPT t htP x hx).symm
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hPT' t htP x hx).symm
  obtain ⟨S, hPS, hTT'S, hfc⟩ := Asc77.E187C.exists_sylow_inf_centralizer (R := P)
    (R' := T ⊔ T') (A := Subgroup.closure ({t} : Set G)) (S := S₀) (le_sup_left.trans hS₀)
    (le_sup_right.trans hS₀) hct
  rw [Subgroup.centralizer_closure] at hfc
  exact ⟨S, P, T, T', h.sylowTri_of_commuting hP hT hT' hPS (le_sup_left.trans hTT'S)
    (le_sup_right.trans hTT'S) hPT hPT' hTT', hfc⟩

theorem sylowTri_of_sylow (h : Tri r Ω K J M t u) (S' : Sylow 2 G) :
    ∃ (g : G) (P T T' : Subgroup G), SylowTri Ω S' (conjSub g K) (conjSub g J) (conjSub g M)
      P T T' (g * t * g⁻¹) (g * u * g⁻¹) := by
  obtain ⟨S, P, T, T', hS, -⟩ := h.exists_std_sylowTri
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  refine ⟨g, conjSub g P, conjSub g T, conjSub g T', ?_⟩
  rw [← hg]
  exact hS.conj h.fam.hyp.conjInvariant g

end Tri

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
