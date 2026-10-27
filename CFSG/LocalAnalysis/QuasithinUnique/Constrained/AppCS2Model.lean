module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem ffIneq' (P : PiData L) {S A : Subgroup G} (hU : IsElemAbelian 2 (blockU L))
    (hUS : blockU L ≤ S) (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsMaxElemAbelian S A) :
    16 ≤ Nat.card (P.im A) * Nat.card (FixΔ (P.im A)) := by
  set K := A ⊓ Subgroup.centralizer (blockU L : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ k ∈ K, ∀ u ∈ blockU L, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe hU hcomm
  have hB1S : K ⊔ blockU L ≤ S := sup_le (inf_le_left.trans hA.1) hUS
  have h1 : Nat.card ↥(K ⊔ blockU L) ≤ Nat.card A := hA.2.2 _ hB1S hB1e
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ blockU L) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  have h4 := P.card_im_mul hAN
  have h5 := P.card_fix hAN
  have h6 := P.card_blockU
  have hkpos : 0 < Nat.card ↥K := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (P.im A)
  set f := Nat.card (FixΔ (P.im A))
  have h7 : Nat.card ↥K * 16 ≤ Nat.card ↥K * (p * f) := by
    calc Nat.card ↥K * 16 = Nat.card ↥(K ⊔ blockU L) * Nat.card ↥(K ⊓ blockU L) := by
          rw [h2, h6]
      _ ≤ Nat.card A * f := Nat.mul_le_mul h1 h3
      _ = Nat.card ↥K * (p * f) := by rw [← h4]; ring
  exact Nat.le_of_mul_le_mul_left h7 hkpos

theorem swapGen_im' (P : PiData L) {S A : Subgroup G} (hU : IsElemAbelian 2 (blockU L))
    (hUS : blockU L ≤ S) (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsMaxElemAbelian S A) :
    ∀ g ∈ P.im A, g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ P.im A ∧ s.IsSwap} :=
  swapGen_of_ff (P.im A) (P.im_elemAbelian hA.2.1).1 (P.im_elemAbelian hA.2.1).2
    (ffIneq' P hU hUS hAN hA)

theorem swapGen_imJ' (P : PiData L) (hU : IsElemAbelian 2 (blockU L)) (hUS : blockU L ≤ S)
    (hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G)) :
    ∀ g ∈ P.im (thompsonJ S),
      g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ P.im (thompsonJ S) ∧ s.IsSwap} := by
  set Cl := Subgroup.closure {s : Perm (Fin 5) | s ∈ P.im (thompsonJ S) ∧ s.IsSwap} with hCl
  have hW : thompsonJ S ≤ (Cl.comap P.π).map (Subgroup.normalizer (L : Set G)).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hJN (GammaExtra.le_thompsonJ hA ha)
    refine Subgroup.mem_map.2 ⟨⟨a, haN⟩, ?_, rfl⟩
    show P.π ⟨a, haN⟩ ∈ Cl
    have hmem : P.π ⟨a, haN⟩ ∈ P.im A := P.pi_mem_im ha
    have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
      (GammaExtra.le_thompsonJ hA).trans hJN
    have := swapGen_im' P hU hUS hAN hA _ hmem
    refine Subgroup.closure_mono ?_ this
    intro s hs
    exact ⟨P.im_mono (GammaExtra.le_thompsonJ hA) hs.1, hs.2⟩
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (P.mem_im).1 hg
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.1 (hW hy)
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact hy'

theorem exists_mem_thompsonJ_pi_ne_one' {J : Subgroup G} (P : PiData L) (hL : IsShort2 L)
    (hth : ⁅L, J⁆ = L) (hJN : J ≤ Subgroup.normalizer (L : Set G)) (hLQ : ¬ L ≤ blockQ L) :
    ∃ y : ↥(Subgroup.normalizer (L : Set G)), (y : G) ∈ J ∧ P.π y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hLQ
  have hLQ' : L ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 L :=
    C1.inf_centralizer_blockU_eq hL le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)
  calc L = ⁅L, J⁆ := hth.symm
    _ ≤ blockQ L := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ y hy
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hJN hy
      have hyL : y * ℓ⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hℓ)
      have hcom : ⁅ℓ, y⁆ = ℓ * (y * ℓ⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have hcL : ⁅ℓ, y⁆ ∈ L := by rw [hcom]; exact mul_mem hℓ hyL
      have hπ : P.π (⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
          ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        have hy1 := hcon ⟨y, hyN⟩ hy
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        simp
      have hc := (P.hker _).1 hπ
      have hcC : ⁅ℓ, y⁆ ∈ Subgroup.centralizer (blockU L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := hc u hu
        have h2 : (((⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
            ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹ :
              ↥(Subgroup.normalizer (L : Set G))) : ↥(Subgroup.normalizer (L : Set G))) : G) =
            ⁅ℓ, y⁆ := by
          simp [commutatorElement_def]
        rw [h2] at h1
        calc u * ⁅ℓ, y⁆ = (⁅ℓ, y⁆ * u * ⁅ℓ, y⁆⁻¹) * ⁅ℓ, y⁆ := by rw [h1]
          _ = ⁅ℓ, y⁆ * u := by group
      have h3 : ⁅ℓ, y⁆ ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hcL, hcC⟩
      rw [hLQ'] at h3
      exact h3

omit [Finite G] in
theorem s2SI_le_normalizer : s2SI S L ≤ Subgroup.normalizer (L : Set G) := fun _ hg => hg.2

omit [Finite G] in
theorem s2SI_le_S : s2SI S L ≤ S := fun _ hg => hg.1

omit [Finite G] in
theorem not_le_blockQ_of_alt5 {L : Subgroup G} (P : A5Pi L) :
    ¬ L ≤ blockQ L := by
  intro hle
  have : Nontrivial (alternatingGroup (Fin 5)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [A5.Delta5.a5_card]; norm_num)
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  obtain ⟨ℓ, rfl⟩ := P.hα a
  apply ha
  have h1 : ℓ ∈ P.α.ker := by
    rw [P.hαk, mem_pCore_iff_mem_blockQ]
    exact hle ℓ.2
  exact h1

theorem card_im_of_sylow {X S₀ : Subgroup G} (P : PiData L) (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf S₀ X)
    (hsurj : Function.Surjective (P.π.comp (Subgroup.inclusion hXN))) :
    Nat.card (P.im S₀) = 8 := by
  have hS' : IsPGroup 2 (S₀.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let Pp : Sylow 2 X := hS'.toSylow hS.2.2
  have h1 := sylow_card_perm_five (Pp.mapSurjective hsurj)
  have h2 : ((Pp.mapSurjective hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) =
      (S₀.subgroupOf X).map (P.π.comp (Subgroup.inclusion hXN)) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : (S₀.subgroupOf X).map (P.π.comp (Subgroup.inclusion hXN)) = P.im S₀ := by
    ext g
    rw [P.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hXN x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hS.1 hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [← h3, ← h2]
  exact h1

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem isPGroup_s2SI : IsPGroup 2 (s2SI S L) := D.hcs.sylow.isPGroup.to_le s2SI_le_S

theorem blockU_le_S : blockU L ≤ S :=
  (C56.blockU_le_pCoreOf_general D.hcs).trans (C56.pCoreOf_le_S D.hcs)

theorem blockU_le_L : blockU L ≤ L := (C1.blockU_le_blockQ D.hL).trans (C1.blockQ_le L)

theorem thompsonJ_le_N : thompsonJ S ≤ Subgroup.normalizer (L : Set G) :=
  C56.le_normalizer_of_commutator_eq D.hcs.thompson

theorem isSylowTwoOf_s2SI_sup : IsSylowTwoOf (s2SI S L) (L ⊔ s2SI S L) := by
  have hN : s2SI S L ≤ Subgroup.normalizer (L : Set G) := s2SI_le_normalizer
  have hSyl : IsSylowTwoOf (S ⊓ L) L := Lin2.isSylowTwoOf_S_inf_L D.hcs
  have hinf : s2SI S L ⊓ L = S ⊓ L := by
    ext x
    constructor
    · rintro ⟨⟨hxS, -⟩, hxL⟩
      exact ⟨hxS, hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨⟨hxS, Subgroup.le_normalizer hxL⟩, hxL⟩
  refine ⟨le_sup_right, D.isPGroup_s2SI, fun hdvd => hSyl.2.2 ?_⟩
  have hsc : L ⊔ s2SI S L = s2SI S L ⊔ L := sup_comm _ _
  rw [hsc] at hdvd
  change 2 ∣ (s2SI S L).relIndex (s2SI S L ⊔ L) at hdvd
  have h1 := C5.card_eq_card_mul_relIndex (le_sup_left : s2SI S L ≤ s2SI S L ⊔ L)
  have h2 := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf] at h2
  have h3 := C5.card_eq_card_mul_relIndex (inf_le_right : S ⊓ L ≤ L)
  have hpos1 : 0 < Nat.card ↥(S ⊓ L) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(s2SI S L) := Nat.card_pos
  have key : (s2SI S L).relIndex (s2SI S L ⊔ L) = (S ⊓ L).relIndex L := by
    have h4 : Nat.card ↥(s2SI S L) * (s2SI S L).relIndex (s2SI S L ⊔ L) * Nat.card ↥(S ⊓ L) =
        Nat.card ↥(s2SI S L) * Nat.card ↥(S ⊓ L) * (S ⊓ L).relIndex L := by
      calc Nat.card ↥(s2SI S L) * (s2SI S L).relIndex (s2SI S L ⊔ L) * Nat.card ↥(S ⊓ L)
          = Nat.card ↥(s2SI S L ⊔ L) * Nat.card ↥(S ⊓ L) := by rw [h1]
        _ = Nat.card ↥(s2SI S L) * Nat.card ↥L := h2
        _ = Nat.card ↥(s2SI S L) * (Nat.card ↥(S ⊓ L) * (S ⊓ L).relIndex L) := by rw [← h3]
        _ = Nat.card ↥(s2SI S L) * Nat.card ↥(S ⊓ L) * (S ⊓ L).relIndex L := by ring
    have h5 : (Nat.card ↥(s2SI S L) * Nat.card ↥(S ⊓ L)) *
        (s2SI S L).relIndex (s2SI S L ⊔ L) =
        (Nat.card ↥(s2SI S L) * Nat.card ↥(S ⊓ L)) * (S ⊓ L).relIndex L := by
      rw [← h4]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos2 hpos1) h5
  rw [key] at hdvd
  exact hdvd

theorem core_J (P : A5Pi L) :
    ∃ τ₁ τ₂ : Perm (Fin 5), τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
      P.im (thompsonJ S) = Subgroup.closure {τ₁, τ₂} ∧ Nat.card (P.im (s2SI S L)) = 8 ∧
      P.im (L ⊔ thompsonJ S) = ⊤ ∧
      (∀ d ∈ P.im (s2SI S L), ∀ j ∈ P.im (thompsonJ S), d * j * d⁻¹ ∈ P.im (thompsonJ S)) ∧
      ∀ g : Perm (Fin 5), (∀ w ∈ FixΔ (P.im (thompsonJ S)), vact g w = w) →
        g ∈ P.im (thompsonJ S) := by
  classical
  have hL := D.hL
  have hJN := D.thompsonJ_le_N
  have hJS₁ : thompsonJ S ≤ s2SI S L := D.thompsonJ_le_s2SI
  have hS₁N : s2SI S L ≤ Subgroup.normalizer (L : Set G) := s2SI_le_normalizer
  have hU := isElemAbelian_blockU hL
  have hUS := D.blockU_le_S
  have hXN : L ⊔ thompsonJ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hJN
  have hX₁N : L ⊔ s2SI S L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hS₁N
  let Dd : PiData L := P.toPiData
  let π := Dd.π
  have hα := P.hα
  have hπα := P.hπα
  have hLQ := not_le_blockQ_of_alt5 P
  obtain ⟨y₀, hy₀J, hy₀⟩ := exists_mem_thompsonJ_pi_ne_one' Dd hL D.hcs.thompson hJN hLQ
  have hJ1 : ∃ j ∈ Dd.im (thompsonJ S), j ≠ 1 := ⟨Dd.π y₀, Dd.pi_mem_im hy₀J, hy₀⟩
  have hJsw := swapGen_imJ' Dd hU hUS hJN
  obtain ⟨t', htJ, htsw⟩ := exists_swap_of_swapGen _ hJ1 hJsw
  have hπX : ∀ σ : Perm (Fin 5), ∃ x : ↥(L ⊔ thompsonJ S), π ⟨x, hXN x.2⟩ = σ := by
    intro σ
    by_cases hs : Equiv.Perm.sign σ = 1
    · obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩, ?_⟩
      have := hπα ℓ ℓ.2
      rw [hℓ] at this
      exact this
    · obtain ⟨y, hyJ, hyt⟩ := (Dd.mem_im).1 htJ
      have hsg : Equiv.Perm.sign (σ * t'⁻¹) = 1 := by
        obtain ⟨a, b, hab, rfl⟩ := htsw
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h hs
        · rw [h]; decide
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ * t'⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hsg⟩
      refine ⟨⟨ℓ, Subgroup.mem_sup_left ℓ.2⟩ * ⟨y, Subgroup.mem_sup_right hyJ⟩, ?_⟩
      have h1 := hπα ℓ ℓ.2
      rw [hℓ] at h1
      have h2 : π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) =
          π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * π y := by
        rw [← map_mul]
      show π (⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ * ⟨(y : G), y.2⟩) = σ
      rw [h2, hyt]
      have h3 : π ⟨(ℓ : G), hXN (Subgroup.mem_sup_left ℓ.2)⟩ = σ * t'⁻¹ := h1
      rw [h3]
      exact inv_mul_cancel_right σ t'
  have hfsurj : Function.Surjective (Dd.π.comp (Subgroup.inclusion hX₁N)) := by
    intro σ
    obtain ⟨x, hx⟩ := hπX σ
    exact ⟨⟨x, sup_le_sup_left hJS₁ L x.2⟩, hx⟩
  have hD8 : Nat.card (Dd.im (s2SI S L)) = 8 :=
    card_im_of_sylow Dd hX₁N D.isSylowTwoOf_s2SI_sup hfsurj
  have hJn : ∀ d ∈ Dd.im (s2SI S L), ∀ j ∈ Dd.im (thompsonJ S),
      d * j * d⁻¹ ∈ Dd.im (thompsonJ S) := by
    intro d hd j hj'
    obtain ⟨s, hs, rfl⟩ := (Dd.mem_im).1 hd
    obtain ⟨y, hy, rfl⟩ := (Dd.mem_im).1 hj'
    have h1 : (s : G) * y * (s : G)⁻¹ ∈ thompsonJ S := thompsonJ_conj_mem hs.1 hy
    have : Dd.π s * Dd.π y * (Dd.π s)⁻¹ = Dd.π (s * y * s⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact Dd.pi_mem_im (K := thompsonJ S) (y := s * y * s⁻¹) (by simpa using h1)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hswap, hfix⟩ :=
    swap_core (Dd.im (s2SI S L)) (Dd.im (thompsonJ S)) hD8 (Dd.im_mono hJS₁) hJn hJ1 hJsw
  refine ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hD8, ?_, hJn, hfix⟩
  refine eq_top_iff.2 fun σ _ => ?_
  obtain ⟨x, hx⟩ := hπX σ
  exact (Dd.mem_im).2 ⟨⟨x, hXN x.2⟩, x.2, hx⟩

theorem exists_std (P : A5Pi L) :
    ∃ P' : A5Pi L, P'.im (thompsonJ S) = Estd ∧ P'.im (s2SI S L) = Dstd ∧
      P'.im (L ⊔ thompsonJ S) = ⊤ := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, hD8, htop, hJn, -⟩ := D.core_J P
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Perm (Fin 5)))).map (MulAut.conj ρ).toMonoidHom =
      Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  have hJ' : (P.conj ρ).im (thompsonJ S) = Estd := by rw [A5Pi.im_conj, hJeq, hcl]
  have hnorm' : ∀ d ∈ (P.conj ρ).im (s2SI S L), ∀ j ∈ (P.conj ρ).im (thompsonJ S),
      d * j * d⁻¹ ∈ (P.conj ρ).im (thompsonJ S) := by
    intro d hd j hj'
    rw [A5Pi.im_conj] at hd hj' ⊢
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hj'
    refine Subgroup.mem_map.2 ⟨d₀ * j₀ * d₀⁻¹, hJn d₀ hd₀ j₀ hj₀, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hle : (P.conj ρ).im (s2SI S L) ≤ Dstd := by
    intro d hd
    rw [mem_Dstd, mem_Dset]
    intro x hx
    have := hnorm' d hd x (by rw [hJ']; exact hx)
    rwa [hJ'] at this
  have hcard : Nat.card ((P.conj ρ).im (s2SI S L)) = 8 := by
    rw [A5Pi.im_conj, Subgroup.card_map_of_injective (MulAut.conj ρ).injective, hD8]
  refine ⟨P.conj ρ, hJ', ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])
  · rw [A5Pi.im_conj, htop, Subgroup.map_top_of_surjective _ (MulAut.conj ρ).surjective]

end Dbl

end CFSG.QuasithinUnique.AppCS2
