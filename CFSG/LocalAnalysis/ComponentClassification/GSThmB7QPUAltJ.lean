module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUAltFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcComp

public section

namespace CFSG.ComponentClassification.GSThmB.QPUAlt

open CFSG Subgroup Equiv Equiv.Perm

theorem autFixed_conj_eq {G : Type*} [Group G] (g : G) :
    TBLit.autFixed (MulAut.conj g) = centralizer ({g} : Set G) := by
  ext x
  rw [Burgoyne.DX.mem_autFixed_iff, mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  · intro h
    rw [← h]
    group

theorem exists_hom_of_mulEquiv {M : Type} [Group M] {n : ℕ}
    (e : M ⧸ center M ≃* alternatingGroup (Fin n)) :
    ∃ ν : M →* alternatingGroup (Fin n), Function.Surjective ν ∧ ν.ker = center M := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center M)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isPComponent_centralizer_of_central {M : Type} [Group M] [Finite M]
    (hZ : IsPGroup 2 (center M)) {n : ℕ} (ν : M →* alternatingGroup (Fin n))
    (hν : Function.Surjective ν) (hker : ν.ker = center M) {t : M} (ht : t * t = 1)
    {J : Subgroup M} (hJt : J ≤ centralizer ({t} : Set M))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) :
    5 ≤ Nat.card {x : Fin n // ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) x = x} ∧
      pPrimeCore 2 J = ⊥ ∧
      ∀ a b c : Fin n, ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) a = a →
        ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) b = b →
        ((ν t : alternatingGroup (Fin n)) : Perm (Fin n)) c = c → a ≠ b → a ≠ c → b ≠ c →
        ∃ j ∈ J, ((ν j : alternatingGroup (Fin n)) : Perm (Fin n)) = swap a b * swap a c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← autFixed_conj_eq] at hJt hJc
  obtain ⟨hJt', hJc'⟩ := Burgoyne.DX.isPComponent_map_autFixed ν hν hker.le (hker ▸ hZ)
    (s := MulAut.conj t) (s' := MulAut.conj (ν t))
    (fun x => by rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]) hJt hJc
  rw [autFixed_conj_eq] at hJt' hJc'
  have hs : ν t * ν t = 1 := by rw [← map_mul, ht, map_one]
  obtain ⟨hdeg, hsimp, hev, h3⟩ := isPComponent_centralizer_alternating hs hJt' hJc'
  refine ⟨hdeg, ?_, fun a b c ha hb hc hab hac hbc => ?_⟩
  ·
    set O := pPrimeCore 2 J with hO
    let νJ := ν.subgroupMap J
    have hνJ : Function.Surjective νJ := ν.subgroupMap_surjective J
    have hOn : (O.map νJ).Normal := Normal.map inferInstance νJ hνJ
    have hOb : O.map νJ = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (O.map νJ) with hb | ht'
      · exact hb
      · exfalso
        have hdvd := card_map_dvd O νJ
        rw [ht', card_top] at hdvd
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
          ((pPrimeCore_coprime_card (p := 2) (G := J)).coprime_dvd_right hdvd)
          (even_iff_two_dvd.mp hev)
    have hO2 : IsPGroup 2 O := by
      intro x
      have hx1 : νJ (x : J) = 1 := by
        have : νJ (x : J) ∈ O.map νJ := ⟨x, x.2, rfl⟩
        rwa [hOb, mem_bot] at this
      have hxZ : ((x : J) : M) ∈ center M := by
        rw [← hker, MonoidHom.mem_ker]
        exact congrArg Subtype.val hx1
      obtain ⟨k, hk⟩ := hZ ⟨_, hxZ⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have h1 := congrArg Subtype.val hk
      simpa using h1
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    have hcop := pPrimeCore_coprime_card (p := 2) (G := J)
    rw [← hO, hk] at hcop
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact card_eq_one.mp hk
    · exfalso
      rw [Nat.coprime_pow_right_iff (Nat.succ_pos k)] at hcop
      norm_num at hcop
  · obtain ⟨x, hx, hxσ⟩ := h3 a b c ha hb hc hab hac hbc
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hx
    exact ⟨j, hj, hxσ⟩

end CFSG.ComponentClassification.GSThmB.QPUAlt
