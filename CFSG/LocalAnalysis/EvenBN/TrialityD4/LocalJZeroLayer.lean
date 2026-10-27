module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoNeighbour

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

section Generic

theorem exists_isPGroup_two_lt_card_of_isQuasisimple_D4 {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : ∃ U : Subgroup Q, IsPGroup 2 U ∧ 2 < Nat.card U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  have : Fintype Q := Fintype.ofFinite Q
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 Q))
  by_contra hcon
  push Not at hcon
  have hS2 : Nat.card S ≤ 2 := hcon S S.isPGroup'
  have heven : Even (Nat.card Q) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact Group.IsPerfect.not_isSolvable Q (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hS : Nat.card S = 2 := by
    have h1 : 2 ∣ Nat.card S := by
      rw [Sylow.card_eq_multiplicity]
      have hpos : 0 < (Nat.card Q).factorization 2 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' (even_iff_two_dvd.1 heven)
      exact dvd_pow_self 2 hpos.ne'
    have h2 : 0 < Nat.card S := Nat.card_pos
    omega
  have hcyc : IsCyclic S := isCyclic_of_prime_card (p := 2) hS
  have heven' : Even (Fintype.card Q) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨-, hsurj, -, hind⟩ := CFSG.LinearGroups.cyclic_sylow_index_two heven' S hcyc
  set ε : Q →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom Q Q) with hε
  have hle : commutator Q ≤ ε.ker := Abelianization.commutator_subset_ker ε
  have hker : ε.ker = ⊤ :=
    top_le_iff.1 ((Group.IsPerfect.commutator_eq_top (G := Q)).symm.le.trans hle)
  rw [hker, Subgroup.index_top] at hind
  exact absurd hind (by norm_num)

theorem le_of_le_sup_oddCore_D4 {Q : Type*} [Group Q] [Finite Q] {A B : Subgroup Q} [B.Normal]
    (hA : ⁅A, A⁆ = A) (hAB : A ≤ B ⊔ CFSG.oddCore Q) : A ≤ B := by
  set ρ := QuotientGroup.mk' B with hρ
  have hle : A.map ρ ≤ (CFSG.oddCore Q).map ρ := by
    calc A.map ρ ≤ (B ⊔ CFSG.oddCore Q).map ρ := map_mono hAB
      _ = (CFSG.oddCore Q).map ρ := by
          rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff B).2 (by rw [hρ, QuotientGroup.ker_mk']),
            bot_sup_eq]
  have hodd : Odd (Nat.card (A.map ρ)) :=
    Odd.of_dvd_nat (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Q)
      ((card_dvd_of_le hle).trans (card_map_dvd (H := CFSG.oddCore Q) (f := ρ)))
  have hsolv : Group.IsSolvable (A.map ρ) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hperf : Group.IsPerfect (A.map ρ) := by
    rw [Subgroup.isPerfect_iff, ← map_commutator, hA]
  have hbot : A.map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial (A.map ρ) := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (A.map ρ) hsolv
  rwa [Subgroup.map_eq_bot_iff, hρ, QuotientGroup.ker_mk'] at hbot

theorem le_map_layer_of_isComponent_D4 {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hNO : ∀ a ∈ CFSG.oddCore Y, ∀ n ∈ N, a * n = n * a)
    {C : Subgroup (Y ⧸ CFSG.oddCore Y)} (hC : CFSG.IsComponent C)
    (hCN : C ≤ N.map (QuotientGroup.mk' (CFSG.oddCore Y))) :
    C ≤ (CFSG.layer Y).map (QuotientGroup.mk' (CFSG.oddCore Y)) := by
  classical
  set π := QuotientGroup.mk' (CFSG.oddCore Y) with hπ
  set Nt := N ⊓ C.comap π with hNt
  let φ : Nt →* C := (π.domRestrict Nt).codRestrict C fun x => (mem_comap.1 x.2.2)
  have hφ : ∀ x : Nt, (φ x : Y ⧸ CFSG.oddCore Y) = π x := fun _ => rfl
  have hφs : Function.Surjective φ := by
    intro c
    obtain ⟨n, hn, hnc⟩ := hCN c.2
    refine ⟨⟨n, hn, (show π n ∈ C by rw [hnc]; exact c.2)⟩, Subtype.ext ?_⟩
    rw [hφ]
    exact hnc
  have hker : φ.ker ≤ center Nt := by
    intro x hx
    have h1 : (x : Y) ∈ CFSG.oddCore Y := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      rw [hφ, OneMemClass.coe_one, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    exact mem_center_iff.2 fun y => Subtype.ext (hNO _ h1 _ y.2.1).symm
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective φ hφs hker
    hC.1.1
  have hq := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective φ hφs hker hC.1
  set C₁ := (commutator Nt).map Nt.subtype with hC₁
  have hC₁ : CFSG.IsComponent C₁ := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator Nt).equivMapOfInjective Nt.subtype Nt.subtype_injective) hq, ?_⟩
    have hNts : Nt.IsSubnormal := (Normal.isSubnormal ‹N.Normal›).inf (hC.2.comap π)
    have hle : C₁ ≤ Nt := map_subtype_le _
    refine IsSubnormal.step C₁ Nt hle hNts ?_
    have : (commutator Nt).Normal := inferInstance
    have e : C₁.subgroupOf Nt = commutator Nt :=
      comap_map_eq_self_of_injective Nt.subtype_injective _
    rw [e]
    exact this
  intro c hc
  obtain ⟨x, hx⟩ := hsurj ⟨c, hc⟩
  refine ⟨((x : Nt) : Y), CFSG.LocalCores.component_le_layer hC₁ ⟨x, x.2, rfl⟩, ?_⟩
  have := congrArg Subtype.val hx
  exact this

theorem layer_eq_normalClosure_D4 {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : ⁅K, K⁆ = K) (hKO : ∀ a ∈ CFSG.oddCore Y, ∀ k ∈ K, a * k = k * a) {s : Y}
    (hs : s * s = 1) (hsK : ∀ k ∈ K, k * s = s * k)
    {Kc : Subgroup (Y ⧸ CFSG.oddCore Y)} (hKc : CFSG.IsComponent Kc) (hZ : center Kc = ⊥)
    (hcomp : ∀ C : Subgroup (Y ⧸ CFSG.oddCore Y), CFSG.IsComponent C →
      C = Kc ∨ C = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    (hKle : K.map (QuotientGroup.mk' (CFSG.oddCore Y)) ≤
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    (hKab : ∃ a ∈ K, ∃ b ∈ K, a * b * a⁻¹ * b⁻¹ ∉ CFSG.oddCore Y) :
    CFSG.layer Y = normalClosure (K : Set Y) ∧
      (∀ a ∈ CFSG.oddCore Y, ∀ e ∈ CFSG.layer Y, a * e = e * a) ∧
      (CFSG.layer Y).map (QuotientGroup.mk' (CFSG.oddCore Y)) =
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom := by
  classical
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  set sb := π s with hsb
  set Kc' := Kc.map (MulAut.conj sb).toMonoidHom with hKc'
  set N := normalClosure (K : Set Y) with hN
  have hKc'c : CFSG.IsComponent Kc' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hZ' : center Kc' = ⊥ := by
    have e := map_center_eq (Kc.equivMapOfInjective (MulAut.conj sb).toMonoidHom
      (MulAut.conj sb).injective)
    rw [hZ, Subgroup.map_bot] at e
    exact e.symm
  have hsb2 : sb * sb = 1 := by rw [hsb, ← map_mul, hs, map_one]
  have hsbinv : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
  have hE : CFSG.layer (Y ⧸ O) = Kc ⊔ Kc' := by
    refine le_antisymm (sSup_le fun C hC => ?_) (sup_le (CFSG.LocalCores.component_le_layer hKc)
      (CFSG.LocalCores.component_le_layer hKc'c))
    rcases hcomp C hC with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hlayN : (CFSG.layer (Y ⧸ O)).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Y ⧸ O)
    exact normal_of_characteristic _
  have hlayYN : (CFSG.layer Y).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Y)
    exact normal_of_characteristic _
  have hconjK : ∀ x ∈ K.map π, sb * x * sb⁻¹ = x := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hsb, ← map_inv, ← map_mul, ← map_mul, ← hsK k hk, mul_inv_cancel_right]
  have hnot : ¬ (K.map π ≤ centralizer (Kc : Set (Y ⧸ O)) ∧
      K.map π ≤ centralizer (Kc' : Set (Y ⧸ O))) := by
    rintro ⟨h1, h2⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hKab
    have h3 : Kc ⊔ Kc' ≤ centralizer (K.map π : Set (Y ⧸ O)) :=
      sup_le (le_centralizer_iff.1 h1) (le_centralizer_iff.1 h2)
    have h5 := mem_centralizer_iff.1 ((hKle.trans h3) ⟨b, hb, rfl⟩) (π a) ⟨a, ha, rfl⟩
    apply hab
    have h6 : π (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h5]
      group
    exact (QuotientGroup.eq_one_iff _).1 h6
  have hboth : K.map π ≤ centralizer (Kc : Set (Y ⧸ O)) →
      K.map π ≤ centralizer (Kc' : Set (Y ⧸ O)) := by
    intro h1 x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have h2 := mem_centralizer_iff.1 (h1 hx) c hc
    have hx' := hconjK x hx
    change sb * c * sb⁻¹ * x = x * (sb * c * sb⁻¹)
    calc sb * c * sb⁻¹ * x = sb * (c * x) * sb⁻¹ := by
          rw [show sb * (c * x) * sb⁻¹ = (sb * c * sb⁻¹) * (sb * x * sb⁻¹) by group, hx']
      _ = sb * (x * c) * sb⁻¹ := by rw [h2]
      _ = x * (sb * c * sb⁻¹) := by
          rw [show sb * (x * c) * sb⁻¹ = (sb * x * sb⁻¹) * (sb * c * sb⁻¹) by group, hx']
  have hboth' : K.map π ≤ centralizer (Kc' : Set (Y ⧸ O)) →
      K.map π ≤ centralizer (Kc : Set (Y ⧸ O)) := by
    intro h1 x hx
    rw [mem_centralizer_iff]
    intro c hc
    have hc' : sb * c * sb⁻¹ ∈ Kc' := ⟨c, hc, rfl⟩
    have h2 := mem_centralizer_iff.1 (h1 hx) _ hc'
    have hx' := hconjK x hx
    calc c * x = sb⁻¹ * ((sb * c * sb⁻¹) * (sb * x * sb⁻¹)) * sb := by group
      _ = sb⁻¹ * ((sb * c * sb⁻¹) * x) * sb := by rw [hx']
      _ = sb⁻¹ * (x * (sb * c * sb⁻¹)) * sb := by rw [h2]
      _ = sb⁻¹ * ((sb * x * sb⁻¹) * (sb * c * sb⁻¹)) * sb := by rw [hx']
      _ = x * c := by group
  set M := normalClosure ((K.map π : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) with hM
  have hNM : N.map π = M := by
    rw [hN, map_normalClosure _ π (QuotientGroup.mk'_surjective O), hM, coe_map]
  have hMle : M ≤ CFSG.layer (Y ⧸ O) :=
    normalClosure_le_normal (fun x hx => (hE.symm ▸ hKle) hx)
  have hCM : ∀ C : Subgroup (Y ⧸ O), CFSG.IsComponent C → center C = ⊥ →
      ¬ K.map π ≤ centralizer (C : Set (Y ⧸ O)) → C ≤ M := by
    intro C hC hCZ hCK
    have hn : (M.subgroupOf C).Normal := Normal.subgroupOf inferInstance C
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.1 hn with htop | hcen
    · intro c hc
      have : (⟨c, hc⟩ : C) ∈ M.subgroupOf C := htop ▸ mem_top _
      exact this
    · exfalso
      rw [hCZ, le_bot_iff] at hcen
      apply hCK
      intro x hx
      rw [mem_centralizer_iff]
      intro c hc
      have hxM : x ∈ M := subset_normalClosure hx
      have hxN : x ∈ normalizer (C : Set (Y ⧸ O)) :=
        CFSG.LocalCores.layer_le_normalizer hC (hMle hxM)
      have h1 : c * x * c⁻¹ * x⁻¹ ∈ M := by
        rw [show c * x * c⁻¹ * x⁻¹ = (c * x * c⁻¹) * x⁻¹ by group]
        exact mul_mem ((inferInstance : M.Normal).conj_mem x hxM c) (inv_mem hxM)
      have h2 : c * x * c⁻¹ * x⁻¹ ∈ C := by
        rw [show c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) by group]
        exact mul_mem hc ((mem_normalizer_iff.1 hxN c⁻¹).1 (inv_mem hc))
      have h3 : (⟨_, h2⟩ : C) ∈ M.subgroupOf C := h1
      rw [hcen, mem_bot] at h3
      have h4 : c * x * c⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
      calc c * x = c * x * c⁻¹ * x⁻¹ * (x * c) := by group
        _ = x * c := by rw [h4, one_mul]
  have hKcM : Kc ≤ M := hCM Kc hKc hZ fun h1 => hnot ⟨h1, hboth h1⟩
  have hKc'M : Kc' ≤ M := hCM Kc' hKc'c hZ' fun h1 => hnot ⟨hboth' h1, h1⟩
  have hNbar : N.map π = Kc ⊔ Kc' :=
    hNM.trans (le_antisymm (hMle.trans hE.le) (sup_le hKcM hKc'M))
  have hNperf : ⁅N, N⁆ = N := by
    refine le_antisymm (commutator_le_left N N) ?_
    have hle : (K : Set Y) ⊆ (⁅N, N⁆ : Subgroup Y) := by
      intro k hk
      rw [← hK] at hk
      exact commutator_mono (le_normalClosure) (le_normalClosure) hk
    exact normalClosure_le_normal hle
  have hNO : ∀ a ∈ O, ∀ n ∈ N, a * n = n * a := by
    have hle : N ≤ centralizer (O : Set Y) :=
      normalClosure_le_normal fun k hk => mem_centralizer_iff.2 fun a ha => hKO a ha k hk
    intro a ha n hn
    exact mem_centralizer_iff.1 (hle hn) a ha
  have hlayO : ∀ C : Subgroup Y, CFSG.IsComponent C → ¬ C ≤ π.ker := by
    intro C hC hCO
    rw [hπ, QuotientGroup.ker_mk'] at hCO
    have hodd : Odd (Nat.card C) := Odd.of_dvd_nat
      (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y) (card_dvd_of_le hCO)
    have : Nontrivial C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
    have : Group.IsPerfect C := hC.1.1
    exact Group.IsPerfect.not_isSolvable C (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have h1 : CFSG.layer Y ≤ N := by
    refine le_of_le_sup_oddCore_D4 CFSG.LocalCores.layer_perfect (sSup_le fun C hC => ?_)
    have hCb : CFSG.IsComponent (C.map π) :=
      ⟨CFSG.LocalCores.isQuasisimple_map hC.1 π (hlayO C hC),
        hC.2.map (QuotientGroup.mk'_surjective O)⟩
    have h2 : C.map π ≤ N.map π := by
      rw [hNbar]
      rcases hcomp _ hCb with h3 | h3 <;> rw [h3]
      · exact le_sup_left
      · exact le_sup_right
    calc C ≤ (C.map π).comap π := le_comap_map _ _
      _ ≤ (N.map π).comap π := comap_mono h2
      _ = N ⊔ O := by rw [comap_map_eq, hπ, QuotientGroup.ker_mk']
  have h2 : N ≤ CFSG.layer Y := by
    refine le_of_le_sup_oddCore_D4 hNperf ?_
    have h3 : Kc ⊔ Kc' ≤ (CFSG.layer Y).map π :=
      sup_le (le_map_layer_of_isComponent_D4 hNO hKc (hNbar.symm ▸ le_sup_left))
        (le_map_layer_of_isComponent_D4 hNO hKc'c (hNbar.symm ▸ le_sup_right))
    calc N ≤ (N.map π).comap π := le_comap_map _ _
      _ ≤ ((CFSG.layer Y).map π).comap π := comap_mono (hNbar.symm ▸ h3)
      _ = CFSG.layer Y ⊔ O := by rw [comap_map_eq, hπ, QuotientGroup.ker_mk']
  have hEN : CFSG.layer Y = N := le_antisymm h1 h2
  refine ⟨hEN, fun a ha e he => hNO a ha e (hEN ▸ he), ?_⟩
  rw [hEN]
  exact hNbar

end Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

@[expose] noncomputable def jZeroLayer {q : ℕ} (d : TrialityD4Data L q) : Subgroup G :=
  CFSG.inSubgroup CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))

namespace Setup

section CountC₁

theorem J₀_map_le_normalizer_yamadaC₁ (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ normalizer (yamadaC₁ d t : Set G) := fun _ hj =>
  le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d
    ⟨h.J₀_map_le_centralizer d hj, map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_V) hj⟩)

theorem J₀_map_le_normalizer_tD (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ normalizer ((d.D.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hj => mem_normalizer_sup (map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_D) hj)
    (mem_normalizer_zpowers_of_comm_D4
      (mem_centralizer_singleton_iff.1 (h.J₀_map_le_centralizer d hj)))

theorem yamadaC₁_le_normalizer_tD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaC₁ d t ≤ normalizer ((d.D.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  obtain ⟨hN, -⟩ := h.yamada_5_3_1_module_all d
  exact (normal_subgroupOf_iff_le_normalizer (h.tD_le_yamadaC₁ d)).1 hN

theorem inv_mul_conj_mem_tD_of_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {a x : G} (ha : a ∈ d.J₀.map L.subtype) (hx : x ∈ yamadaC₁ d t) :
    x⁻¹ * (a * x * a⁻¹) ∈ d.D.map L.subtype ⊔ zpowers t := by
  obtain ⟨hN, φ, -, hφc⟩ := h.yamada_5_3_1_module_all d
  have haC : a ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    ⟨h.J₀_map_le_centralizer d ha, map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_V) ha⟩
  obtain ⟨hy, hφy⟩ := hφc a haC ⟨x, hx⟩
  have hv : (φ (QuotientGroup.mk ⟨x, hx⟩) : G) ∈ d.Y.map L.subtype :=
    map_mono d.V_le_Y (φ (QuotientGroup.mk ⟨x, hx⟩)).2
  have hav := mem_centralizer_iff.1 (J₀_map_le_centralizer_Y d ha) _ hv
  have haz : a * (φ (QuotientGroup.mk ⟨x, hx⟩) : G) * a⁻¹ = φ (QuotientGroup.mk ⟨x, hx⟩) := by
    rw [← hav, mul_inv_cancel_right]
  have h3 : (QuotientGroup.mk (⟨x, hx⟩ : yamadaC₁ d t) : yamadaC₁ d t ⧸
      (d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t)) =
        QuotientGroup.mk (⟨a * x * a⁻¹, hy⟩ : yamadaC₁ d t) :=
    (φ.injective (Subtype.ext (hφy.trans haz))).symm
  have h4 : (⟨x, hx⟩ : yamadaC₁ d t)⁻¹ * ⟨a * x * a⁻¹, hy⟩ ∈
      (d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t) := QuotientGroup.eq.1 h3
  exact h4

omit [Finite G] in
theorem D_map_inf_centralizer_J₀ {q : ℕ} (d : TrialityD4Data L q) :
    d.D.map L.subtype ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) =
      d.sylowJ₀.map L.subtype := by
  apply le_antisymm
  · rintro x ⟨⟨n, hn, rfl⟩, hxc⟩
    exact ⟨n, ⟨d.D_le_S hn, mem_centralizer_of_coe_mem hxc⟩, rfl⟩
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨⟨n, ?_, rfl⟩, coe_mem_centralizer_of_mem hn.2⟩
    obtain ⟨a, b, c, rfl⟩ := d.mem_sylowJ₀_iff.1 hn
    exact mul_mem (mul_mem (d.x₂_mem_D a) (d.F_le_D (d.x₅_mem_F b))) (d.F_le_D (d.x₆_mem_F c))

theorem tD_inf_centralizer_J₀ (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    (d.D.map L.subtype ⊔ zpowers t) ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) =
      d.sylowJ₀.map L.subtype ⊔ zpowers t := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hx with h1 | h1
    · exact mem_sup_left ((D_map_inf_centralizer_J₀ d).le ⟨h1, hxc⟩)
    · have htx : t * x ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
        mul_mem (h.t_mem_centralizer_J₀ d) hxc
      exact (h.mem_sup_zpowers_iff (map_subtype_le _)).2
        (Or.inr ((D_map_inf_centralizer_J₀ d).le ⟨h1, htx⟩))
  · refine sup_le ?_ ((zpowers_le).2 ⟨mem_sup_right (mem_zpowers t), h.t_mem_centralizer_J₀ d⟩)
    rw [← D_map_inf_centralizer_J₀ d]
    exact inf_le_inf_right _ le_sup_left

theorem relIndex_tD_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (d.D.map L.subtype ⊔ zpowers t).relIndex (yamadaC₁ d t) = 2 ^ f := by
  obtain ⟨hN, φ, -⟩ := h.yamada_5_3_1_module_all d
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr φ.toEquiv,
    card_map_of_injective L.subtype_injective, d.card_V]

theorem card_yamadaC₁_inf_centralizer_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    Nat.card (yamadaC₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :
      Subgroup G) = 2 * (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : ¬ 2 ∣ Nat.card (d.J₀.map L.subtype : Subgroup G) := by
    rw [card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀.not_two_dvd_nat
  rw [card_inf_centralizer_eq_of_coprime_D4 (P := yamadaC₁ d t) (h.tD_le_yamadaC₁ d)
    (h.yamadaC₁_le_normalizer_tD d) (h.J₀_map_le_normalizer_yamadaC₁ d)
    (h.J₀_map_le_normalizer_tD d) (h.isPGroup_tD d) hA
    (fun a ha x hx => h.inv_mul_conj_mem_tD_of_mem_yamadaC₁ d ha hx),
    h.tD_inf_centralizer_J₀ d, h.card_sup_zpowers (map_subtype_le _),
    card_map_of_injective L.subtype_injective, d.card_sylowJ₀, h.relIndex_tD_yamadaC₁ d]
  ring

theorem exists_mem_yamadaC₁_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∃ x ∈ yamadaC₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G),
      ∃ v ∈ d.V.map L.subtype, v ≠ 1 ∧ x * t * x⁻¹ = t * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hC, hconj, hV⟩ := h.yamada_5_3_1_all d
  set H := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  have hex : ∃ x ∈ yamadaC₁ d t ⊓ H, x ∉ centralizer ({t} : Set G) := by
    by_contra hne
    push Not at hne
    have hle : yamadaC₁ d t ⊓ H ≤ d.sylowJ₀.map L.subtype ⊔ zpowers t := by
      intro x hx
      rw [← h.tD_inf_centralizer_J₀ d, ← hC]
      exact ⟨⟨hx.1, hne x hx⟩, hx.2⟩
    have h1 := card_le_of_le hle
    rw [h.card_yamadaC₁_inf_centralizer_J₀ d, h.card_sup_zpowers (map_subtype_le _),
      card_map_of_injective L.subtype_injective, d.card_sylowJ₀] at h1
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
    have : 0 < (2 ^ f) ^ 3 := by positivity
    nlinarith
  obtain ⟨x, hx, hxt⟩ := hex
  have hmem : x * t * x⁻¹ ∈ {y | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = y} := ⟨x, hx.1, rfl⟩
  rw [hconj] at hmem
  obtain ⟨v, hv, hve⟩ := hmem
  have hve : t * v = x * t * x⁻¹ := hve
  refine ⟨x, hx, v, hv, fun hv1 => hxt ?_, hve.symm⟩
  rw [hv1, mul_one] at hve
  rw [mem_centralizer_singleton_iff]
  calc x * t = x * t * x⁻¹ * x := by group
    _ = t * x := by rw [← hve]

end CountC₁

section OddCore

theorem le_normalizer_oddCore_map (H : Subgroup G) :
    H ≤ normalizer (((CFSG.oddCore H).map H.subtype : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun n hn => ?_
  obtain ⟨n', hn', rfl⟩ := hn
  exact ⟨⟨x, hx⟩ * n' * (⟨x, hx⟩ : H)⁻¹, (CFSG.oddCore_normal (G := H)).conj_mem n' hn' _, rfl⟩

theorem odd_card_oddCore_map (H : Subgroup G) :
    Odd (Nat.card ((CFSG.oddCore H).map H.subtype : Subgroup G)) := by
  rw [card_map_of_injective H.subtype_injective]
  exact CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore H

theorem mem_centralizer_leviJ₀_of_mem_oddCore {q : ℕ} (d : TrialityD4Data L q)
    {c : G} (hcO : c ∈ (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G))).map (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype)
    (hcK : c ∈ d.leviJ₀.map L.subtype) :
    c ∈ centralizer ((d.leviJ₀.map L.subtype : Subgroup G) : Set G) := by
  set H := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  set OG := (CFSG.oddCore H).map H.subtype with hOG
  set KG := d.leviJ₀.map L.subtype with hKG
  have hKH : KG ≤ H := leviJ₀_map_le_centralizer_J₀ d
  have hN : (OG.subgroupOf KG).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (le_normalizer_oddCore_map H (hKH g.2)) n).1 hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_leviJ₀_map d) hN with
    htop | hcen
  · exfalso
    have hx : d.x₂ 1 ∈ d.leviJ₀ := d.U₂_le_leviJ₀ (d.x₂_mem_U₂ 1)
    have hxO : ((⟨(d.x₂ 1 : G), ⟨_, hx, rfl⟩⟩ : KG) : G) ∈ OG := by
      have : (⟨(d.x₂ 1 : G), ⟨_, hx, rfl⟩⟩ : KG) ∈ OG.subgroupOf KG := htop ▸ mem_top _
      exact this
    have h2 : orderOf (⟨(d.x₂ 1 : G), hxO⟩ : OG) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      refine orderOf_eq_prime (by rw [sq, ← d.x₂_add, d.add_self_Γ₀, d.x₂_zero]) ?_
      intro h1
      have := d.x₂_injective (h1.trans d.x₂_zero.symm)
      exact one_ne_zero this
    have h3 := orderOf_dvd_natCard (⟨(d.x₂ 1 : G), hxO⟩ : OG)
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 (odd_card_oddCore_map H)) (even_iff_two_dvd.2 h3)
  · have : (⟨c, hcK⟩ : KG) ∈ center KG := hcen (by rw [mem_subgroupOf]; exact hcO)
    rw [mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val ((mem_center_iff.1 this ⟨k, hk⟩))

theorem commute_leviJ₀_of_mem_oddCore (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {a : G}
    (ha : a ∈ (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G))).map (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype)
    (hat : a * t = t * a) {k : G} (hk : k ∈ d.leviJ₀.map L.subtype) : a * k = k * a := by
  set H := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  set OG := (CFSG.oddCore H).map H.subtype with hOG
  set KG := d.leviJ₀.map L.subtype with hKG
  have hKH : KG ≤ H := leviJ₀_map_le_centralizer_J₀ d
  have hOH : OG ≤ H := map_subtype_le _
  have hcomm : ∀ b ∈ OG, b * t = t * b → ∀ k ∈ KG, b * k * b⁻¹ * k⁻¹ ∈
      centralizer (KG : Set G) := by
    intro b hb hbt k hk
    have hbN : b ∈ normalizer (KG : Set G) :=
      h.centralizer_J₀_inf_centralizer_le_normalizer_leviJ₀ d
        ⟨hOH hb, mem_centralizer_singleton_iff.2 hbt⟩
    have h1 : b * k * b⁻¹ * k⁻¹ ∈ KG :=
      mul_mem ((mem_normalizer_iff.1 hbN k).1 hk) (inv_mem hk)
    have h2 : b * k * b⁻¹ * k⁻¹ ∈ OG := by
      rw [show b * k * b⁻¹ * k⁻¹ = b * (k * b⁻¹ * k⁻¹) by group]
      exact mul_mem hb ((mem_normalizer_iff.1 (le_normalizer_oddCore_map H (hKH hk)) _).1
        (inv_mem hb))
    exact mem_centralizer_leviJ₀_of_mem_oddCore d h2 h1
  have hle : ⁅KG, zpowers a⁆ ≤ centralizer (KG : Set G) := by
    rw [commutator_le]
    intro k hk b hb
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    have hbt : a ^ n * t = t * a ^ n := (Commute.zpow_left (hat : Commute a t) n).eq
    have := hcomm (a ^ n) (zpow_mem ha n) hbt k hk
    rw [← commutatorElement_def, ← commutatorElement_inv] at this
    exact (inv_mem_iff).1 this
  have hbot : ⁅⁅KG, zpowers a⁆, KG⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 hle
  have hperf : Group.IsPerfect KG := (isQuasisimple_leviJ₀_map d).1
  have h1 := CFSG.LocalCores.perfect_double_commutator hperf hbot
  have h2 : ⁅k, a⁆ = 1 := by
    have := commutator_mem_commutator hk (mem_zpowers a)
    rw [h1] at this
    exact this
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem oddCore_commute_leviJ₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {a k : G}
    (ha : a ∈ (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G))).map (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)).subtype)
    (hk : k ∈ d.leviJ₀.map L.subtype) : a * k = k * a := by
  set H := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) with hH
  set OG := (CFSG.oddCore H).map H.subtype with hOG
  set KG := d.leviJ₀.map L.subtype with hKG
  have hKH : KG ≤ H := leviJ₀_map_le_centralizer_J₀ d
  obtain ⟨x, hx, v, hv, hv1, hxv⟩ := h.exists_mem_yamadaC₁_conj_eq d
  obtain ⟨v', hv', rfl⟩ := hv
  have hxv : x * t * x⁻¹ = t * (v' : G) := hxv
  have hv1 : (v' : G) ≠ 1 := hv1
  have hvK : (v' : G) ∈ KG := ⟨v', d.U₆_le_leviJ₀ hv', rfl⟩
  have hvL : (v' : G) ∈ L := v'.2
  have hvv : (v' : G) * v' = 1 := by
    obtain ⟨c, rfl⟩ := hv'
    rw [← Subgroup.coe_mul, d.x₆_mul_self, Subgroup.coe_one]
  have htv : t * v' = v' * t := (mem_centralizer_iff.1 h.htL _ hvL).symm
  have hxvc : x * v' = v' * x :=
    (mem_centralizer_iff.1 ((h.yamada_5_3_1_all d).2.2.2.2.2 hx.1) _ ⟨v', hv', rfl⟩).symm
  have hvO : ∀ y ∈ OG, (v' : G) * y = y * v' := by
    refine CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.commute_of_four_group_centralizers
      (odd_card_oddCore_map H) h.t_mul_t hvv htv h.t_ne_one hv1
      (fun e => h.t_not_mem_L (e ▸ hvL)) (le_normalizer_oddCore_map H (h.t_mem_centralizer_J₀ d))
      (le_normalizer_oddCore_map H (hKH hvK)) ?_ ?_ ?_
    · intro y hy hyt
      exact (h.commute_leviJ₀_of_mem_oddCore d hy hyt hvK).symm
    · intro y _ hyv
      exact hyv.symm
    · intro y hy hytv
      rw [← hxv] at hytv
      have hy' : x⁻¹ * y * x ∈ OG := by
        have := (mem_normalizer_iff.1 (le_normalizer_oddCore_map H (inv_mem hx.2)) y).1 hy
        rwa [inv_inv] at this
      have hyt' : x⁻¹ * y * x * t = t * (x⁻¹ * y * x) := by
        have e : y * (x * t * x⁻¹) = x * t * x⁻¹ * y := hytv
        calc x⁻¹ * y * x * t = x⁻¹ * (y * (x * t * x⁻¹)) * x := by group
          _ = x⁻¹ * (x * t * x⁻¹ * y) * x := by rw [e]
          _ = t * (x⁻¹ * y * x) := by group
      have h1 := h.commute_leviJ₀_of_mem_oddCore d hy' hyt' hvK
      calc (v' : G) * y = v' * x * (x⁻¹ * y * x) * x⁻¹ := by group
        _ = x * v' * (x⁻¹ * y * x) * x⁻¹ := by rw [hxvc]
        _ = x * (x⁻¹ * y * x * v') * x⁻¹ := by rw [h1]; group
        _ = y * (x * v') * x⁻¹ := by group
        _ = y * v' := by rw [hxvc]; group
  have hT : ((centralizer (OG : Set G)).subgroupOf KG).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    rw [mem_centralizer_iff] at hn ⊢
    intro y hy
    have hgy : (g : G)⁻¹ * y * g ∈ OG := by
      have := (mem_normalizer_iff.1 (le_normalizer_oddCore_map H (hKH (inv_mem g.2))) y).1 hy
      rwa [inv_inv] at this
    have := hn _ hgy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (g * n * (g : G)⁻¹) = g * ((g : G)⁻¹ * y * g * n) * (g : G)⁻¹ := by group
      _ = g * (n * ((g : G)⁻¹ * y * g)) * (g : G)⁻¹ := by rw [this]
      _ = g * n * (g : G)⁻¹ * y := by group⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_leviJ₀_map d) hT with
    htop | hcen
  · have hk' : (⟨k, hk⟩ : KG) ∈ (centralizer (OG : Set G)).subgroupOf KG := htop ▸ mem_top _
    rw [mem_subgroupOf] at hk'
    exact (mem_centralizer_iff.1 hk' a ha)
  · exfalso
    have hvc : (⟨v', hvK⟩ : KG) ∈ center KG := hcen (by
      rw [mem_subgroupOf, mem_centralizer_iff]
      intro y hy
      exact (hvO y hy).symm)
    have hvc' : (v' : G) ∈ centralizer (KG : Set G) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val ((mem_center_iff.1 hvc ⟨k, hk⟩))
    have hvJ : v' ∈ centralizer (d.J₀ : Set L) := d.Y_le_centralizer_J₀ (d.V_le_Y hv')
    have hv2 : v' ^ 2 ^ 1 = 1 := Subtype.ext (by
      rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
      exact hvv)
    have := d.eq_one_of_mem_centralizer_leviJ₀ hvJ (mem_centralizer_of_coe_mem hvc') hv2
    exact hv1 (by rw [this, Subgroup.coe_one])

end OddCore

section Components

theorem isComponent_eq_of_le_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))}
    (hKc : CFSG.IsComponent Kc)
    (hKb : ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom)
    {C' : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))}
    (hC' : CFSG.IsComponent C') :
    C' = Kc ∨ C' = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
        ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom := by
  set π := QuotientGroup.mk' (CFSG.oddCore
    (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) with hπ
  set tb := π ⟨t, h.t_mem_centralizer_J₀ d⟩ with htb
  have hKc' : CFSG.IsComponent (Kc.map (MulAut.conj tb).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tb) hKc
  rcases CFSG.LocalCores.distinct_components_commute hC' hKc with h1 | h1
  · exact Or.inl h1
  rcases CFSG.LocalCores.distinct_components_commute hC' hKc' with h2 | h2
  · exact Or.inr h2
  exfalso
  obtain ⟨-, hsyl, -⟩ := h.yamada_5_4_hr7 d
  have hC'K : C' ≤ centralizer ((((d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map π :
        Subgroup _) : Set _) := by
    refine le_trans ?_ (centralizer_le hKb)
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h1))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h2))
  obtain ⟨U, hU, hU2⟩ := exists_isPGroup_two_lt_card_of_isQuasisimple_D4 hC'.1
  have h3 := hsyl (U.map C'.subtype) (hU.map _) ((map_subtype_le U).trans hC'K)
  rw [card_map_of_injective C'.subtype_injective] at h3
  omega

end Components

section Layer

omit [Finite G] in
theorem map_conj_eq_self_D4 {Y : Type*} [Group Y] {K : Subgroup Y} {g : Y} [Finite K]
    (hg : g ∈ normalizer (K : Set Y)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    rwa [inv_inv] at this

omit [Finite G] in
theorem not_mem_oddCore_of_mul_self_D4 {Y : Type*} [Group Y] [Finite Y] {y : Y}
    (hy : y * y = 1) (hy1 : y ≠ 1) : y ∉ CFSG.oddCore Y := by
  intro hyO
  have h2 : orderOf (⟨y, hyO⟩ : CFSG.oddCore Y) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have h3 := orderOf_dvd_natCard (⟨y, hyO⟩ : CFSG.oddCore Y)
  rw [h2] at h3
  exact (Nat.not_even_iff_odd.2
    (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y))
    (even_iff_two_dvd.2 h3)

@[expose] def LayerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : Prop :=
  ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
    CFSG.IsComponent Kc ∧ center Kc = ⊥ ∧
    (∀ C : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent C → C = Kc ∨ C = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom) ∧
    CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) =
      normalClosure (((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
          Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) :
            Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ∧
    (∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      ∀ e ∈ CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        a * e = e * a) ∧
    (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) =
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
    QuotientGroup.mk' (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
        ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
    ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
      (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥))

theorem yamada_5_4_layer_of_cat (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f)
    (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧ center Kc = ⊥ ∧
      (∀ C : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
          CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
        CFSG.IsComponent C → C = Kc ∨ C = Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom) ∧
      CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) =
        normalClosure (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
            Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) :
              Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ∧
      (∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        ∀ e ∈ CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
          a * e = e * a) ∧
      (CFSG.layer (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) =
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      QuotientGroup.mk' (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥)) := by
  obtain ⟨Kc, hKc, hKb, hcase⟩ := h.yamada_5_4_of_cat d hf hcat
  have hKH : d.leviJ₀.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    leviJ₀_map_le_centralizer_J₀ d
  have hKperf : ⁅(d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        (d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))⁆ =
      (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) := by
    have hKG : ⁅d.leviJ₀.map L.subtype, d.leviJ₀.map L.subtype⁆ = d.leviJ₀.map L.subtype :=
      Subgroup.isPerfect_iff.1 (isQuasisimple_leviJ₀_map d).1
    apply Subgroup.map_injective (centralizer ((d.J₀.map L.subtype : Subgroup G) :
      Set G)).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hKH, hKG]
  have hKO : ∀ a ∈ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      ∀ k ∈ (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)), a * k = k * a :=
    fun a ha k hk => Subtype.ext (h.oddCore_commute_leviJ₀ d ⟨a, ha, rfl⟩ hk)
  have hs : (⟨t, h.t_mem_centralizer_J₀ d⟩ :
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) * ⟨t, h.t_mem_centralizer_J₀ d⟩ =
        1 := Subtype.ext h.t_mul_t
  have hsK : ∀ k ∈ (d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
        k * ⟨t, h.t_mem_centralizer_J₀ d⟩ = ⟨t, h.t_mem_centralizer_J₀ d⟩ * k :=
    fun k hk => Subtype.ext (mem_centralizer_iff.1 h.htL _ (map_subtype_le _ hk))
  have hZ : center Kc = ⊥ := by
    rcases hcase with ⟨-, -, -, -, hZ, -⟩ | ⟨-, -, hZ, -⟩ <;> exact hZ
  have hcomp := fun C hC => h.isComponent_eq_of_le_sup d hKc hKb (C' := C) hC
  have hKab : ∃ a ∈ (d.leviJ₀.map L.subtype).subgroupOf
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      ∃ b ∈ (d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)),
      a * b * a⁻¹ * b⁻¹ ∉ CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) :
        Set G)) := by
    have h2 : d.x₂ 1 ∈ d.leviJ₀ := d.U₂_le_leviJ₀ (d.x₂_mem_U₂ 1)
    have h5 : d.x₅ 1 ∈ d.leviJ₀ := d.U₅_le_leviJ₀ (d.x₅_mem_U₅ 1)
    set a : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
      ⟨(d.x₂ 1 : G), hKH ⟨_, h2, rfl⟩⟩ with ha
    set b : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
      ⟨(d.x₅ 1 : G), hKH ⟨_, h5, rfl⟩⟩ with hb
    refine ⟨a, ⟨_, h2, rfl⟩, b, ⟨_, h5, rfl⟩, ?_⟩
    have e : ((a * b * a⁻¹ * b⁻¹ : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
        G) = ((d.x₆ 1 : L) : G) := by
      show (d.x₂ 1 : G) * d.x₅ 1 * (d.x₂ 1 : G)⁻¹ * (d.x₅ 1 : G)⁻¹ = d.x₆ 1
      rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, ← commutatorElement_def, d.comm₂₅, mul_one]
    refine not_mem_oddCore_of_mul_self_D4 (Subtype.ext ?_) (fun h1 => ?_)
    · rw [Subgroup.coe_mul, e, ← Subgroup.coe_mul, d.x₆_mul_self, Subgroup.coe_one,
        OneMemClass.coe_one]
    · have := congrArg Subtype.val h1
      rw [e, OneMemClass.coe_one] at this
      have h6 : d.x₆ 1 = 1 := Subtype.ext this
      exact one_ne_zero (d.x₆_injective (h6.trans d.x₆_zero.symm))
  obtain ⟨hEN, hEO, hEmap⟩ := layer_eq_normalClosure_D4 hKperf hKO hs hsK hKc hZ hcomp hKb hKab
  refine ⟨Kc, hKc, hZ, hcomp, hEN, hEO, hEmap, ?_, ?_⟩
  · rcases hcase with ⟨heq, -, htK, -, -, -⟩ | ⟨hne, hcomm, -, -⟩
    · rw [heq, sup_idem]
      exact htK
    · intro ht
      apply hne
      refine map_conj_eq_self_D4 ?_
      have hle : Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≤ normalizer (Kc : Set _) :=
        sup_le le_normalizer ((le_centralizer_iff.1
          (commutator_eq_bot_iff_le_centralizer.1 hcomm)).trans
            (Subgroup.centralizer_le_normalizer _))
      exact hle ht
  · rcases hcase with ⟨heq, -, -, -, -, hlie⟩ | ⟨hne, hcomm, -, -⟩
    · exact Or.inl ⟨heq, hlie⟩
    · exact Or.inr ⟨hne, hcomm⟩

theorem layerHyp_of_cat (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f)
    (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) : h.LayerHyp d :=
  h.yamada_5_4_layer_of_cat d hf hcat

theorem leviJ₀_map_le_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.leviJ₀.map L.subtype ≤ jZeroLayer d := by
  obtain ⟨Kc, -, -, -, hEN, -⟩ := hlay
  intro k hk
  refine ⟨⟨k, leviJ₀_map_le_centralizer_J₀ d hk⟩, ?_, rfl⟩
  rw [hEN]
  exact subset_normalClosure (show _ ∈ (d.leviJ₀.map L.subtype).subgroupOf _ from hk)

theorem t_not_mem_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ jZeroLayer d := by
  obtain ⟨Kc, -, -, -, -, -, hEmap, ht, -⟩ := hlay
  rintro ⟨e, he, hte⟩
  apply ht
  rw [← hEmap]
  refine ⟨e, he, ?_⟩
  congr 1
  exact Subtype.ext hte

end Layer

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
