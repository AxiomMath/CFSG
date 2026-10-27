module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Key
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBGraphForm
open scoped commutatorElement

theorem dl_of_mem_Om {h : S} (hh : h ∈ Om) : dl h = h := by
  have : Om ≤ MonoidHom.eqLocus dl.toMonoidHom (MonoidHom.id S) := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact dl_Ps
    · exact dl_bs
  exact this hh

theorem conj_cancel (Q h : S) : Q⁻¹ * (Q * h * Q⁻¹) * Q = h := by group

@[expose] def OmQ (Q : S) : Subgroup S := Om.map (MulAut.conj Q).toMonoidHom

theorem mem_OmQ {Q w : S} : w ∈ OmQ Q ↔ Q⁻¹ * w * Q ∈ Om := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_cancel]
    exact hh
  · intro h
    refine ⟨Q⁻¹ * w * Q, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem OmQ_perfect (Q : S) : Group.IsPerfect (OmQ Q) := by
  have : Group.IsPerfect Om := Subgroup.isPerfect_iff.2 Om_perfect
  exact Group.IsPerfect.map _

theorem cent_OmQ (Q : S) : Subgroup.centralizer (OmQ Q : Set S) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hP : Q * Ps * Q⁻¹ ∈ OmQ Q := mem_OmQ.2 (by rw [conj_cancel]; exact Ps_mem)
  have hb : Q * bs * Q⁻¹ ∈ OmQ Q := mem_OmQ.2 (by rw [conj_cancel]; exact bs_mem)
  have h1 := Subgroup.mem_centralizer_iff.1 hy _ hP
  have h2 := Subgroup.mem_centralizer_iff.1 hy _ hb
  have h3 : (Q⁻¹ * y * Q) * Ps = Ps * (Q⁻¹ * y * Q) := by
    calc (Q⁻¹ * y * Q) * Ps = Q⁻¹ * (y * (Q * Ps * Q⁻¹)) * Q := by group
      _ = Q⁻¹ * ((Q * Ps * Q⁻¹) * y) * Q := by rw [← h1]
      _ = Ps * (Q⁻¹ * y * Q) := by group
  have h4 : (Q⁻¹ * y * Q) * bs = bs * (Q⁻¹ * y * Q) := by
    calc (Q⁻¹ * y * Q) * bs = Q⁻¹ * (y * (Q * bs * Q⁻¹)) * Q := by group
      _ = Q⁻¹ * ((Q * bs * Q⁻¹) * y) * Q := by rw [← h2]
      _ = bs * (Q⁻¹ * y * Q) := by group
  have h5 := cent_Om _ h3 h4
  calc y = Q * (Q⁻¹ * y * Q) * Q⁻¹ := by group
    _ = 1 := by rw [h5]; group

theorem tau_fix_OmQ (Q : S) (τ : MulAut S) (hτ : ∀ g : S, τ g = Q * dl (Q⁻¹ * g * Q) * Q⁻¹) :
    ∀ w ∈ OmQ Q, τ w = w := by
  intro w hw
  have hh := mem_OmQ.1 hw
  rw [hτ, dl_of_mem_Om hh]
  group

theorem patL5_main (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatL5 X K) :
    (∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) →
        Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2) ∧
      (∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u) := by
  obtain ⟨⟨eK⟩, hmodel⟩ := hpat
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  obtain ⟨φ⟩ : Nonempty (↥X ≃* S) :=
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 F hcard2)⟩
  have hZ : Subgroup.center ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : φ a ∈ Subgroup.center S := (mem_center_iff_equiv φ a).2 ha
    rw [center_S, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (φ.injective (by rw [h1, map_one]))
  set π : ↥X →* S := φ.toMonoidHom with hπdef
  have hπapp : ∀ x, π x = φ x := fun x => rfl
  have hπ : Function.Surjective π := φ.surjective
  have hker : π.ker = Subgroup.center ↥X := by
    rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff π).2 φ.injective
  have hX : Group.IsPerfect ↥X := hXq.1
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hK]
    exact perfectResidualOf_le _
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self π hπ hker ht ht2
  have hα1 := quotAct_ne_one π hπ hker ht hXq hcomm
  have hfixK : ∀ k : ↥K, quotAct π hπ hker ht (π (Subgroup.inclusion hKX k)) =
      π (Subgroup.inclusion hKX k) := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply π hπ hker ht _ _ hy
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 (by rw [hKcard]; norm_num)
  have hz : orderOf (π (Subgroup.inclusion hKX z₀)) = 5 := by
    rw [orderOf_injective π φ.injective, orderOf_injective _ (Subgroup.inclusion_injective hKX),
      hz₀]
  set τ := quotAct π hπ hker ht with hτdef
  obtain ⟨Q, hQ⟩ := key_involution τ hα2 hα1 _ hz (hfixK z₀)
  have hperfΩ : Group.IsPerfect ↥((OmQ Q).map (X.subtype.comp φ.symm.toMonoidHom)) := by
    have := OmQ_perfect Q
    exact Group.IsPerfect.map _
  have hΩle : (OmQ Q).map (X.subtype.comp φ.symm.toMonoidHom) ≤
      X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(φ.symm w).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hτw : τ w = w := tau_fix_OmQ Q τ hQ w hw
    obtain ⟨y, hy⟩ : ∃ y : X, (y : G) = t * ((φ.symm w : X) : G) * t⁻¹ :=
      ⟨conjAut X t ht _, coe_conjAut X ht _⟩
    have hαx := quotAct_apply π hπ hker ht (φ.symm w) y hy
    have hπw : π (φ.symm w) = w := by rw [hπapp, MulEquiv.apply_symm_apply]
    rw [hπw, hτw] at hαx
    have h2 : y = φ.symm w := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      exact (hπapp y ▸ hαx).symm
    have h3 : t * ((φ.symm w : X) : G) * t⁻¹ = ((φ.symm w : X) : G) := by rw [← hy, h2]
    show ((φ.symm w : X) : G) * t = t * ((φ.symm w : X) : G)
    calc ((φ.symm w : X) : G) * t = (t * ((φ.symm w : X) : G) * t⁻¹) * t := by rw [h3]
      _ = t * ((φ.symm w : X) : G) := by group
  have hΩK : ∀ w ∈ OmQ Q, ((φ.symm w : ↥X) : G) ∈ K := by
    intro w hw
    have h1 : (OmQ Q).map (X.subtype.comp φ.symm.toMonoidHom) ≤ K := by
      rw [hK]
      exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _
        hperfΩ hΩle
    exact h1 ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  ·
    intro Y hYn hYc
    have hB : ∀ β ∈ (actHom π hπ hker Y hYn).range, ∀ w ∈ OmQ Q, β w = w := by
      rintro _ ⟨y, rfl⟩ w hw
      have hk := hΩK w hw
      have hcomm' : ((φ.symm w : ↥X) : G) * (y : G) = (y : G) * ((φ.symm w : ↥X) : G) :=
        Subgroup.mem_centralizer_iff.mp (hYc y.2) _ hk
      have h1 := actHom_fix π hπ hker Y hYn hcomm'
      rwa [hπapp, MulEquiv.apply_symm_apply] at h1
    have hcard := card_le_two_of_centralizer_trivial card_outer_S (OmQ Q) (cent_OmQ Q) _ hB
    rw [relIndex_eq_card_range π hπ hker Y hYn hX]
    exact hcard
  ·
    intro u huK hu2
    by_cases hu1 : u = 1
    · exact ⟨1, X.one_mem, by rw [hu1]; simp⟩
    obtain ⟨x₀, hx₀⟩ := twist_witness Q τ hQ
    have hu₁mem : (Q * bs * Q⁻¹) ∈ OmQ Q := mem_OmQ.2 (by rw [conj_cancel]; exact bs_mem)
    obtain ⟨u₁, hu₁def⟩ : ∃ u₁ : G, u₁ = ((φ.symm (Q * bs * Q⁻¹) : ↥X) : G) := ⟨_, rfl⟩
    have hu₁K : u₁ ∈ K := by rw [hu₁def]; exact hΩK _ hu₁mem
    obtain ⟨y, hy⟩ : ∃ y : X, (y : G) = t * ((φ.symm x₀ : X) : G) * t⁻¹ :=
      ⟨conjAut X t ht _, coe_conjAut X ht _⟩
    have hαx := quotAct_apply π hπ hker ht (φ.symm x₀) y hy
    have hπx : π (φ.symm x₀) = x₀ := by rw [hπapp, MulEquiv.apply_symm_apply]
    rw [hπx] at hαx
    have hyx : y⁻¹ * φ.symm x₀ = φ.symm (Q * bs * Q⁻¹) := by
      apply φ.injective
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      rw [← hπapp y, ← hαx]
      exact hx₀
    have h3 : (t * ((φ.symm x₀ : X) : G) * t⁻¹)⁻¹ * ((φ.symm x₀ : X) : G) = u₁ := by
      have := congrArg Subtype.val hyx
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy] at this
      rw [hu₁def]
      exact this
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h4 : ((φ.symm x₀ : X) : G)⁻¹ * t * ((φ.symm x₀ : X) : G) = t * u₁ := by
      have h5 : ((φ.symm x₀ : X) : G)⁻¹ * t⁻¹ * ((φ.symm x₀ : X) : G) = t⁻¹ * u₁ := by
        calc ((φ.symm x₀ : X) : G)⁻¹ * t⁻¹ * ((φ.symm x₀ : X) : G)
            = t⁻¹ * ((t * ((φ.symm x₀ : X) : G) * t⁻¹)⁻¹ * ((φ.symm x₀ : X) : G)) := by group
          _ = t⁻¹ * u₁ := by rw [h3]
      rw [hinv] at h5
      exact h5
    have hbs2 : bs * bs = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact bm_sq)
    have hbs1 : bs ≠ 1 := by
      intro h
      have := congrArg Subtype.val h
      have h' : bm = 1 := this
      revert h'
      decide
    have hu₁2 : u₁ * u₁ = 1 := by
      have h1 : φ.symm (Q * bs * Q⁻¹) * φ.symm (Q * bs * Q⁻¹) = 1 := by
        rw [← map_mul]
        have : Q * bs * Q⁻¹ * (Q * bs * Q⁻¹) = 1 := by
          calc Q * bs * Q⁻¹ * (Q * bs * Q⁻¹) = Q * (bs * bs) * Q⁻¹ := by group
            _ = 1 := by rw [hbs2]; group
        rw [this, map_one]
      rw [hu₁def, ← Subgroup.coe_mul, h1]
      rfl
    have hu₁1 : u₁ ≠ 1 := by
      intro h
      rw [hu₁def] at h
      have h1 : φ.symm (Q * bs * Q⁻¹) = 1 := Subtype.ext h
      have h2 : Q * bs * Q⁻¹ = 1 := by
        have := congrArg φ h1
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      apply hbs1
      calc bs = Q⁻¹ * (Q * bs * Q⁻¹) * Q := by group
        _ = 1 := by rw [h2]; group
    obtain ⟨k, hk⟩ := invol_conj_of_equiv eK (u := (⟨u₁, hu₁K⟩ : ↥K)) (v := (⟨u, huK⟩ : ↥K))
      (Subtype.ext hu₁2) (fun h => hu₁1 (congrArg Subtype.val h)) (Subtype.ext hu2)
      (fun h => hu1 (congrArg Subtype.val h))
    have hk' : (k : G) * u₁ * (k : G)⁻¹ = u := congrArg Subtype.val hk
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    refine ⟨(k : G) * ((φ.symm x₀ : X) : G) * (k : G)⁻¹,
      X.mul_mem (X.mul_mem (hKX k.2) (φ.symm x₀).2) (X.inv_mem (hKX k.2)), ?_⟩
    have hktinv : (k : G)⁻¹ * t * k = t := by
      calc (k : G)⁻¹ * t * k = (k : G)⁻¹ * (t * k) := by group
        _ = (k : G)⁻¹ * (k * t) := by rw [hkt]
        _ = t := by group
    calc ((k : G) * ((φ.symm x₀ : X) : G) * (k : G)⁻¹)⁻¹ * t *
          ((k : G) * ((φ.symm x₀ : X) : G) * (k : G)⁻¹)
        = (k : G) * (((φ.symm x₀ : X) : G)⁻¹ * ((k : G)⁻¹ * t * k) * ((φ.symm x₀ : X) : G)) *
            (k : G)⁻¹ := by group
      _ = (k : G) * (((φ.symm x₀ : X) : G)⁻¹ * t * ((φ.symm x₀ : X) : G)) * (k : G)⁻¹ := by
        rw [hktinv]
      _ = (k : G) * (t * u₁) * (k : G)⁻¹ := by rw [h4]
      _ = t * ((k : G) * u₁ * (k : G)⁻¹) := by
        calc (k : G) * (t * u₁) * (k : G)⁻¹ = ((k : G) * t) * u₁ * (k : G)⁻¹ := by group
          _ = (t * k) * u₁ * (k : G)⁻¹ := by rw [hkt]
          _ = t * ((k : G) * u₁ * (k : G)⁻¹) := by group
      _ = t * u := by rw [hk']

theorem tabAutCent_patL5 (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatL5 X K) (Y : Subgroup G) (hYn : Y ≤ Subgroup.normalizer (X : Set G))
    (hYc : Y ≤ Subgroup.centralizer (K : Set G)) :
    (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 :=
  (patL5_main G X K t hXq ht ht2 hcomm hK hpat).1 Y hYn hYc

theorem tabConj_patL5 (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatL5 X K) :
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u :=
  (patL5_main G X K t hXq ht ht2 hcomm hK hpat).2

end CFSG.QuasithinUnique.Id2519.Tab.L5
