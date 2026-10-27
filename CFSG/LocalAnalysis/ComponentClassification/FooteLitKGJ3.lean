module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGA5
public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.GH74.Generic.S45.PerfWitSpec
public import Certificates.Certificate5148

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45

theorem no_component_of_perfect {C : Type*} [Group C] [Finite C] [Group.IsPerfect C]
    {K : Subgroup C} (hK : IsComponent K) (hZ : center ↥K = ⊥)
    (hcard : Nat.card C < Nat.card ↥K * Nat.card ↥K) {j : ℕ} (hj : 1 ≤ j)
    (hdiv : Nat.card C = Nat.card ↥K * 2 ^ j) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : K.Normal := ⟨fun n hn c => by
    set K' := K.map (MulAut.conj c).toMonoidHom with hK'def
    have hK' : IsComponent K' := LocalCores.isComponent_map_mulEquiv _ hK
    have hmem : c * n * c⁻¹ ∈ K' := ⟨n, hn, by simp⟩
    rcases LocalCores.distinct_components_commute hK hK' with h | h
    · rwa [← h] at hmem
    · exfalso
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hcomm : ∀ (a : K) (b : K'), Commute (K.subtype a) (K'.subtype b) := fun a b =>
        ((mem_centralizer_iff.mp (hle a.2)) b b.2).symm
      have hdisj : K ⊓ K' = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxK, hxK'⟩ := mem_inf.mp hx
        have hxZ : (⟨x, hxK⟩ : K) ∈ center K := by
          rw [mem_center_iff]
          intro y
          exact Subtype.ext ((mem_centralizer_iff.mp (hle y.2)) x hxK').symm
        rw [hZ, mem_bot] at hxZ
        exact mem_bot.mpr (congrArg Subtype.val hxZ)
      have hinj : Function.Injective (MonoidHom.noncommCoprod K.subtype K'.subtype hcomm) :=
        (MonoidHom.noncommCoprod_injective _ _ hcomm).2 ⟨K.subtype_injective,
          K'.subtype_injective, by rw [range_subtype, range_subtype, disjoint_iff]; exact hdisj⟩
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, Subgroup.card_map_of_injective (MulAut.conj c).injective] at h1
      omega⟩
  have hq : Nat.card (C ⧸ K) = 2 ^ j := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hdiv] at h
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hKpos (by rw [mul_comm]; exact h.symm)
  have hnil : Group.IsNilpotent (C ⧸ K) := (IsPGroup.of_card hq).isNilpotent
  have : Nontrivial (C ⧸ K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hq]
    exact Nat.one_lt_two_pow (by omega)
  exact Group.IsPerfect.not_isNilpotent (G := C ⧸ K) hnil

theorem noFooteComponent_of_perfect {G : Type} [Group G]
    [Finite G] {j : ℕ} (hj : 1 ≤ j) (hj3600 : 60 * 2 ^ j < 3600)
    (h60 : ∀ N, IsSmallOrder N → N ∣ 60 * 2 ^ j → N = 60)
    (hC : ∀ t : G, orderOf t = 2 → Group.IsPerfect ↥(centralizer ({t} : Set G)) ∧
      Nat.card ↥(centralizer ({t} : Set G)) = 60 * 2 ^ j) :
    NoFooteComponent G := by
  intro L hL
  obtain ⟨t, ht2, hLC, hLp⟩ := hL.1
  obtain ⟨hperf, hcardC⟩ := hC t ht2
  have hLc : Nat.card L ∣ 60 * 2 ^ j := hcardC ▸ Subgroup.card_dvd_of_le hLC
  obtain ⟨hZQ, ⟨eQ⟩⟩ := center_eq_bot_and_nonempty_alt5 hL hLc h60
  have hQ := isQuasisimple_quotient_of_isPComponent hLC hLp
  have hQ60 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = 60 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have hO : pPrimeCore 2 ↥L = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L)
    rw [hQ60] at h
    have hdvd : Nat.card ↥(pPrimeCore 2 ↥L) ∣ 2 ^ j :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num) (h ▸ hLc)
    exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd
      ((pPrimeCore_coprime_card (p := 2) (G := ↥L)).pow_left j).symm hdvd)
  let e : ↥L ≃* ↥L ⧸ pPrimeCore 2 ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)
  set K := L.subgroupOf (centralizer ({t} : Set G))
  let e₀ : ↥L ≃* ↥K := (subgroupOfEquivOfLe hLC).symm
  obtain ⟨-, -, hs, -⟩ := hLp
  have hK : IsComponent K :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv e₀ (LocalCores.isQuasisimple_of_mulEquiv e.symm hQ), hs⟩
  have hZK : center ↥K = ⊥ :=
    center_eq_bot_of_mulEquiv e₀.symm (center_eq_bot_of_mulEquiv e hZQ)
  have hK60 : Nat.card ↥K = 60 := by
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_congr e.toEquiv, hQ60]
  exact no_component_of_perfect hK hZK (by rw [hcardC, hK60]; omega) hj (by rw [hcardC, hK60])

theorem j3P_centralizer_perfect_card
    {τ : Equiv.Perm (Fin 6156)} (hτP : τ ∈ j3P) (hτ : orderOf τ = 2) :
    ⁅j3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 6156))),
        j3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 6156)))⁆ =
      j3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 6156))) ∧
      Nat.card ↥(j3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 6156)))) = 1920 := by
  obtain ⟨-, -, -, hrows, hcover, -, hshape, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, hτg⟩ := hcover τ (Subgroup.mem_sup_left hτP) hτ
  obtain ⟨-, -, hrouter, hCr, hcard, -⟩ := hrows r hr
  have hrP : tp 6156 r.rep ∈ j3P := by
    have : tp 6156 r.rep = g⁻¹ * τ * g := by rw [hτg]; group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hτP) hg
  have hrout : r.outer = false := by
    by_contra hne
    exact (hrouter.1 (by simpa using hne)) hrP
  have hr0 : r.centOrder = 1920 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        j3Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map_of_mem hr
    rw [hshape] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · rw [hrout] at h
      exact absurd h (by decide)
  have hw : perfWitOK 6156 r.centGens j3PerfWit2A = true := by
    have h := List.all_eq_true.1 Certificates.certificate5148.1 r hr
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | h
    · exact absurd hr0 h
    · exact h
  have hperf : ⁅j3C r, j3C r⁆ = j3C r := (perfWitOK_spec (by norm_num) hw).1
  rw [hCr] at hperf
  have hmap := map_conj_inf_centralizer_of_mem j3P hg (tp 6156 r.rep)
  rw [← hτg] at hmap
  refine ⟨?_, ?_⟩
  · rw [← hmap, ← Subgroup.map_commutator, hperf]
  · rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hr0]

theorem centralizer_perfect_card_of_J3
    {G : Type} [Group G]
    (hG : Blueprint.NativeSporadic.IsSporadic G .J3) (t : G) (ht : orderOf t = 2) :
    Group.IsPerfect ↥(centralizer ({t} : Set G)) ∧
      Nat.card ↥(centralizer ({t} : Set G)) = 1920 := by
  have hG' : Nonempty (G ≃* Blueprint.NativeSporadic.J3) := hG
  obtain ⟨e⟩ := hG'
  set θ : G ≃* ↥j3P := e.trans j3PermEquiv
  set u : Equiv.Perm (Fin 6156) := (θ t : Equiv.Perm (Fin 6156)) with hudef
  have huP : u ∈ j3P := (θ t).2
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  have hφ : Function.Injective (j3P.subtype.comp θ.toMonoidHom) :=
    j3P.subtype_injective.comp θ.injective
  have hmap : (centralizer ({t} : Set G)).map (j3P.subtype.comp θ.toMonoidHom) =
      j3P ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 6156))) := by
    rw [← Subgroup.map_map, map_centralizer_equiv θ t, map_centralizer_subtype]
    rfl
  obtain ⟨hperf, hcard⟩ := j3P_centralizer_perfect_card huP hu2
  refine ⟨Subgroup.isPerfect_iff.mpr ?_, ?_⟩
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, hmap, hperf]
  · rw [← Subgroup.card_map_of_injective hφ, hmap, hcard]

theorem footeKnownSmall_J3
    (G : Type) [Group G]
    [Finite G] (hG : Blueprint.NativeSporadic.IsSporadic G .J3) : FooteKnownSmall G :=
  FooteKnownSmall.of_no (noFooteComponent_of_perfect (j := 5) (by norm_num) (by norm_num)
    (eq_of_isSmallOrder_dvd (q₁ := 16) (by norm_num) (by norm_num) (by decide) (by norm_num)
      (by norm_num))
    fun t ht => by
      obtain ⟨h1, h2⟩ := centralizer_perfect_card_of_J3 hG t ht
      exact ⟨h1, by rw [h2]; norm_num⟩)

end CFSG.ComponentClassification.FooteLit.KG
