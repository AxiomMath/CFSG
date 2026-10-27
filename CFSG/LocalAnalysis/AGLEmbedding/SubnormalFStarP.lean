module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.Quasithin.Background.F6ComponentBound

public section

namespace CFSG.AGLEmbedding

theorem eq_bot_of_isSubnormal_of_coprime_of_isCharacteristicP {B : Type*} [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hC : Subgroup.centralizer (CFSG.pCore p B : Set B) ≤ CFSG.pCore p B)
    {V : Subgroup B} (hV : V.IsSubnormal) (hcop : Nat.Coprime p (Nat.card V)) :
    V = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : CFSG.IsCharacteristicP p B := hC
  exact CFSG.Quasithin.F6.eq_bot_of_isSubnormal_of_coprime (D := B) p
    (CFSG.pPrimeCore_eq_bot_of_isCharacteristicP B p hchar) hV hcop

private theorem pCore_two_map_eq_bot_of_surjective {H B : Type*} [Group H] [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Subgroup.centralizer (CFSG.pCore p B : Set B) ≤ CFSG.pCore p B)
    (φ : H →* B) (hφ : Function.Surjective φ) {V : Subgroup H} (hV : V.IsSubnormal) :
    ((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).map φ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO₂sub : ((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).IsSubnormal :=
    (CFSG.pCore_normal (p := 2) (G := ↥V)).isSubnormal.trans' hV
  have hO₂map_sub : (((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).map φ).IsSubnormal :=
    Subgroup.IsSubnormal.map hφ hO₂sub
  have hO₂map_p : IsPGroup 2 (((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).map φ) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥V)).map V.subtype |>.map φ
  have hO₂map_cop : Nat.Coprime p
      (Nat.card (((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).map φ)) := by
    obtain ⟨n, hn⟩ := hO₂map_p.exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right n
  exact eq_bot_of_isSubnormal_of_coprime_of_isCharacteristicP hp hC hO₂map_sub hO₂map_cop

private theorem map_eq_bot_of_isQuasisimple_quotient_pCore_two {H B : Type*} [Group H] [Group B]
    [Finite B] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Subgroup.centralizer (CFSG.pCore p B : Set B) ≤ CFSG.pCore p B)
    (φ : H →* B) (hφ : Function.Surjective φ) {V : Subgroup H} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple (↥V ⧸ CFSG.pCore 2 ↥V)) :
    V.map φ = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hO₂map_bot : ((CFSG.pCore 2 ↥V : Subgroup ↥V).map V.subtype).map φ = ⊥ :=
    pCore_two_map_eq_bot_of_surjective hp hp2 hC φ hφ hV
  have hO₂ker : (CFSG.pCore 2 ↥V : Subgroup ↥V) ≤ (φ.comp V.subtype).ker := by
    refine (Subgroup.map_eq_bot_iff _).mp ?_
    simpa only [← Subgroup.map_map] using hO₂map_bot
  let φ' : ↥V →* ↥(V.map φ) :=
    (φ.comp V.subtype).codRestrict (V.map φ) fun x => Subgroup.mem_map_of_mem φ x.2
  have hφ'surj : Function.Surjective φ' := by
    rintro ⟨w, hw⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    exact ⟨⟨v, hv⟩, Subtype.ext rfl⟩
  have hφ'ker : (CFSG.pCore 2 ↥V : Subgroup ↥V) ≤ φ'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (MonoidHom.mem_ker.mp (hO₂ker hx))
  let g : (↥V ⧸ CFSG.pCore 2 ↥V) →* ↥(V.map φ) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥V) φ' hφ'ker
  have hgsurj : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective (CFSG.pCore 2 ↥V) φ' hφ'surj hφ'ker
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hVq g.normal_ker with htop | hcen
  · have hsub : Subsingleton ↥(V.map φ) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hgsurj a
      obtain ⟨y, rfl⟩ := hgsurj b
      have hx : g x = 1 := by
        have hmem : x ∈ g.ker := htop ▸ Subgroup.mem_top x
        simpa using hmem
      have hy : g y = 1 := by
        have hmem : y ∈ g.ker := htop ▸ Subgroup.mem_top y
        simpa using hmem
      exact hx.trans hy.symm
    exact Subgroup.eq_bot_of_subsingleton _
  · have hWq : CFSG.IsQuasisimple ↥(V.map φ) :=
      CFSG.LocalCores.isQuasisimple_of_surjective hVq g hgsurj hcen
    have hWsub : (V.map φ).IsSubnormal := Subgroup.IsSubnormal.map hφ hV
    have hcomp : CFSG.IsComponent (V.map φ) := ⟨hWq, hWsub⟩
    have hle : V.map φ ≤ CFSG.layer B := CFSG.LocalCores.component_le_layer hcomp
    rw [CFSG.layer_eq_bot_of_isCharacteristicP B p hC] at hle
    exact le_bot_iff.mp hle

theorem le_of_isQuasisimple_quotient_pCore_two {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Subgroup.centralizer (CFSG.pCore p (H ⧸ N) : Set (H ⧸ N)) ≤
      CFSG.pCore p (H ⧸ N))
    {V : Subgroup H} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple (↥V ⧸ CFSG.pCore 2 ↥V)) :
    V ≤ N := by
  have hmap : V.map (QuotientGroup.mk' N) = ⊥ :=
    map_eq_bot_of_isQuasisimple_quotient_pCore_two hp hp2 hC
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hV hVq
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  exact hmap

end CFSG.AGLEmbedding
