module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Struct

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace Twin1711

section Main

variable {G : Type} [Group G]

theorem QuasiE4.conj {X : Subgroup G} (hQ : QuasiE4 X) (g : G) : QuasiE4 (conjSub g X) := by
  obtain ⟨hperf, Q, _, f, hf, hker, hcen, hQ⟩ := hQ
  let e : ↥(conjSub g X) ≃* ↥X :=
    (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  refine ⟨?_, Q, inferInstance, f.comp e.toMonoidHom, hf.comp e.surjective, ?_, ?_, hQ⟩
  · show ⁅X.map (MulAut.conj g).toMonoidHom, X.map (MulAut.conj g).toMonoidHom⁆ =
      X.map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_commutator, hperf]
  · rw [← MonoidHom.comap_ker]
    exact hker.comap_of_injective _ e.injective
  · intro x hx
    rw [← MonoidHom.comap_ker] at hx
    have hx' := hcen hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply e.injective
    simp only [map_mul]
    exact hx' (e y)
end Main

section Final

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {π : Set (Subgroup G)} {z g : G}

theorem not_quasiE4 (hT1 : Fin1711Sandwich) (hT2 : Fin1711Pairing) (h : Cfg' Ω K π z g)
    (hQ : QuasiE4 (piGen π)) : False := by
  have h2 := h.swap
  have e1 : conjSub g⁻¹ (conjSub g K) = K := conjSub_inv_conjSub g K
  have e2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  have hQ' : QuasiE4 (piGen (conjSub g '' π)) := by
    rw [piGen_conj]; exact hQ.conj g
  have hMD1 := h.memberData hQ
  have hMD2 : MemberData (piGen (conjSub g '' π)) K z := by
    have := h2.memberData hQ'
    rwa [e1, e2] at this
  obtain ⟨hc1, hB1⟩ := hT1 G (piGen π) (conjSub g K) (g * z * g⁻¹) _ _ hMD1 h.sandwichData
  obtain ⟨hc2, -⟩ := hT1 G (piGen (conjSub g '' π)) (conjSub g⁻¹ (conjSub g K))
    (g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹) _ _ (h2.memberData hQ') h2.sandwichData
  have P1 := hT2 G (piGen π) (conjSub g K) (g * z * g⁻¹) hMD1 hc1
  have P2 := hT2 G (piGen (conjSub g '' π)) K z hMD2 hc2
  have hβ : (betaOf (nbrAdj Ω) Ω π).ncard = 2 := by
    rw [← Set.ncard_image_of_injective _ (CFSG.ClassicalInvolution.Generic.conjSub_injective g)]
    exact hB1
  have hKβ : K ∈ betaOf (nbrAdj Ω) Ω π :=
    ⟨h.mem, fun M hM => adj_of_mem_isMaxOrb h.std.graph h.max hM⟩
  have hxo2 : xOrbit (piGen (conjSub g '' π)) K = conjSub g '' π := by
    have := h2.xOrbit_eq
    rwa [e1] at this
  have hxo1 := h.xOrbit_eq
  have hdiff : 2 ≤ (commNbrs (piGen (conjSub g '' π)) K \ betaOf (nbrAdj Ω) Ω π).ncard := by
    have := Set.ncard_le_ncard_sdiff_add_ncard (commNbrs (piGen (conjSub g '' π)) K)
      (betaOf (nbrAdj Ω) Ω π) (Set.toFinite _)
    have h4 := P2.1
    omega
  have hdiff' : 1 < (commNbrs (piGen (conjSub g '' π)) K \ betaOf (nbrAdj Ω) Ω π).ncard := by
    omega
  obtain ⟨J₂, J₃, hJ₂, hJ₃, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hdiff'
  have key : ∀ J ∈ commNbrs (piGen (conjSub g '' π)) K \ betaOf (nbrAdj Ω) Ω π,
      J ∈ commNbrs (piGen π) (conjSub g K) ∧ J ∈ Ω := by
    rintro J ⟨⟨hJo, hJc⟩, hJβ⟩
    have hJg : J ∈ conjSub g '' π := by rw [← hxo2]; exact hJo
    have hJne : J ≠ K := fun e => hJβ (e ▸ hKβ)
    have hcomm : Commutes K J := hJc.resolve_left hJne
    have hadj2 := adj_of_mem_isMaxOrb h2.std.graph h2.max hJg
    have hJΩ : J ∈ Ω := hadj2.2.1
    have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
      intro j hj
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have := hcomm k hk j hj
        rw [← this, mul_inv_cancel_right]
        exact hk
      · intro hx
        have h1 := hcomm _ hx j hj
        have h3 : j * k = j * (j * k * j⁻¹) := by
          calc j * k = (j * k * j⁻¹) * j := by group
            _ = j * (j * k * j⁻¹) := h1
        have h4 : k = j * k * j⁻¹ := mul_left_cancel h3
        rw [h4]
        exact hx
    have hKJ : nbrAdj Ω K J :=
      ⟨h.mem, (mem_omegaNbr_iff h.std.hyp h.std.two).mpr ⟨hJΩ, hJne, hJN⟩⟩
    have hJπ : J ∈ π := by
      by_contra hJπ
      exact hJβ (h.std.nbr_diff_subset_beta h.max hKJ hJπ)
    have hRY : conjSub g K ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
      (h.std.conj_le_inf_centralizer h.max h.conj).trans inf_le_right
    have hJY : J ≤ conjSub g (piGen π) := by
      rw [← piGen_conj]; exact le_piGen hJg
    refine ⟨⟨by rw [hxo1]; exact hJπ, Or.inr ?_⟩, hJΩ⟩
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hRY ha) b (hJY hb)).symm
  obtain ⟨hJ₂X, hJ₂Ω⟩ := key J₂ hJ₂
  obtain ⟨hJ₃X, hJ₃Ω⟩ := key J₃ hJ₃
  obtain ⟨u₂, hu₂⟩ := (h.std.hyp.omega1 J₂ hJ₂Ω).1
  obtain ⟨u₃, hu₃⟩ := (h.std.hyp.omega1 J₃ hJ₃Ω).1
  obtain ⟨hne1, hX⟩ := P1.2 J₂ hJ₂X J₃ hJ₃X hne u₂ u₃ hu₂ hu₃
  obtain ⟨-, hY⟩ := P2.2 J₂ hJ₂.1 J₃ hJ₃.1 hne u₂ u₃ hu₂ hu₃
  have hcen : u₂ * u₃ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro a
    have : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.centralizer ({u₂ * u₃} : Set G) := by
      refine iSup₂_le fun M hM => ?_
      rcases hM with hM | hM
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hX x (le_piGen hM hx)
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hY x (le_piGen hM hx)
    rw [h.generate] at this
    exact Subgroup.mem_centralizer_singleton_iff.mp (this (Subgroup.mem_top a))
  rw [h.center, Subgroup.mem_bot] at hcen
  apply hne1
  calc u₂ = u₂ * (u₃ * u₃) := by rw [hu₃.sq, mul_one]
    _ = (u₂ * u₃) * u₃ := by group
    _ = u₃ := by rw [hcen, one_mul]

theorem mem_of_inf_ne_bot {J P : Subgroup G} {u : G} (hJ2 : IsPGroup 2 J)
    (hu : IsUniqueInvolution J u) (h : J ⊓ P ≠ ⊥) : u ∈ P := by
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hxJ : (x : G) ∈ J := (Subgroup.mem_inf.mp x.2).1
  have hxP : (x : G) ∈ P := (Subgroup.mem_inf.mp x.2).2
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext e)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hJ2) ⟨(x : G), hxJ⟩
  have hk' : orderOf (x : G) = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hx1' (orderOf_eq_one_iff.mp (by simpa using hk'))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
  have hyJ : (x : G) ^ (2 ^ m) ∈ J := J.pow_mem hxJ _
  have hyP : (x : G) ^ (2 ^ m) ∈ P := P.pow_mem hxP _
  have hy2 : (x : G) ^ (2 ^ m) * (x : G) ^ (2 ^ m) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hk']
    exact pow_orderOf_eq_one _
  rcases hu.unique _ hyJ hy2 with h1 | h1
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hk'] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  · rwa [h1] at hyP

theorem Cfg'.quasiE4_of_surj (h : Cfg' Ω K π z g) {w : G}
    (hw : IsUniqueInvolution (conjSub g K) w) {X : Subgroup G} (hX : piGen π = X) (hwX : w ∈ X)
    (hperf : ⁅X, X⁆ = X)
    {Q : Type} [Group Q] (F : ↥X →* Q) (hF : Function.Surjective F)
    (hker : IsPGroup 2 ↥F.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1)
    (ht : F ⟨w, hwX⟩ ≠ 1) : QuasiE4 X := by
  subst hX
  have hwe : w = g * z * g⁻¹ := hw.eq h.R_inv
  subst hwe
  refine ⟨hperf, Q, inferInstance, F, hF, hker, ?_, hQ⟩
  let PG : Subgroup G := F.ker.map (piGen π).subtype
  have hPGX : PG ≤ piGen π := Subgroup.map_subtype_le _
  have hPG2 : IsPGroup 2 ↥PG := IsPGroup.map hker (piGen π).subtype
  have hconj : ∀ y ∈ piGen π, ∀ p ∈ PG, y * p * y⁻¹ ∈ PG := by
    rintro y hy _ ⟨p, hp, rfl⟩
    exact ⟨⟨y, hy⟩ * p * ⟨y, hy⟩⁻¹, (MonoidHom.normal_ker F).conj_mem p hp ⟨y, hy⟩, rfl⟩
  have hPGn : ∀ y ∈ piGen π, conjSub y PG = PG := by
    intro y hy
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hconj y hy _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hconj y⁻¹ ((piGen π).inv_mem hy) _ hx
      simpa [mul_assoc] using this
  have hxo := h.xOrbit_eq
  have hcen : ∀ J ∈ π, J ≤ Subgroup.centralizer (PG : Set G) := by
    intro J hJ
    have hJΩ : J ∈ Ω := (adj_of_mem_isMaxOrb h.std.graph h.max hJ).2.1
    obtain ⟨u, hu⟩ := (h.std.hyp.omega1 J hJΩ).1
    have hJX : J ≤ piGen π := le_piGen hJ
    have huPG : u ∉ PG := by
      intro huP
      rw [← hxo] at hJ
      obtain ⟨a, ha, rfl⟩ := hJ
      have hua : u = a * (g * z * g⁻¹) * a⁻¹ := hu.eq (h.R_inv.conj a)
      have htP : g * z * g⁻¹ ∈ PG := by
        have := hconj a⁻¹ ((piGen π).inv_mem ha) _ huP
        rw [hua] at this
        simpa [mul_assoc] using this
      obtain ⟨p, hp, hpe⟩ := htP
      apply ht
      have : p = ⟨g * z * g⁻¹, hwX⟩ := Subtype.ext hpe
      rw [← this]
      exact hp
    have hJP : J ⊓ PG = ⊥ := by
      by_contra hne
      exact huPG (mem_of_inf_ne_bot (h.std.two J hJΩ) hu hne)
    have hc := comm613Gen h.std.hyp (mem_RSet_of_isPGroup hJΩ (h.std.two J hJΩ)) hJX hPGX hPGn hJP
    rw [oddCoreOf_eq_bot_of_isPGroup hPG2, le_bot_iff] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hXc : piGen π ≤ Subgroup.centralizer (PG : Set G) := piGen_le hcen
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro y
  have := Subgroup.mem_centralizer_iff.mp (hXc y.2) p ⟨p, hp, rfl⟩
  exact Subtype.ext this.symm

end Final

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
