module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Group
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

theorem cyc_of_sylow_dvd_le {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Dh Kh : Subgroup X} (hle : Dh ≤ Kh) (hcyc : ∀ A ≤ Dh, IsPGroup p A → IsCyclic A)
    (hdvd : ∀ k, p ^ k ∣ Nat.card Kh → p ^ k ∣ Nat.card Dh) :
    ∀ A ≤ Kh, IsPGroup p A → IsCyclic A := by
  intro A hA hAp
  have hcard : Nat.card (Dh.subgroupOf Kh) = Nat.card Dh :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 : IsCyclic (A.subgroupOf Kh) := by
    refine cyc_of_sylow_dvd (K := ↥Kh) (p := p) hp (Dh := Dh.subgroupOf Kh) ?_ ?_
      (A.subgroupOf Kh) ?_
    · intro B hB hBp
      have hBm : B.map Kh.subtype ≤ Dh := by
        rintro _ ⟨b, hb, rfl⟩
        exact hB hb
      have : IsCyclic ↥(B.map Kh.subtype) := hcyc _ hBm (hBp.map Kh.subtype)
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective B Kh.subtype Kh.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    · intro k hk
      rw [hcard]
      exact hdvd k hk
    · exact hAp.comap_subtype (K := Kh)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hA).toMonoidHom
    (MulEquiv.surjective _)

theorem exists_centCycBar {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParabE L J) {p : ℕ} (hp : p.Prime) {D : Subgroup Y} (hDp : ⁅D, D⁆ = D)
    (hDJ : D ≤ J ⊔ Subgroup.centralizer (L : Set Y))
    (hDcyc : ∀ A : Subgroup Y, A ≤ D → IsPGroup p A → IsCyclic A)
    (hDpart : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ k : ℕ, p ^ k ∣ Nat.card V →
      p ^ k ∣ Nat.card D)
    {x : Y} (hxD : x ∈ D) (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (L : Set Y))
    (hxW : ∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) →
      W = ⊥) :
    ∃ ρ : ↥(J ⊔ Subgroup.centralizer (L : Set Y)) →* ↥L ⧸ Subgroup.center ↥L,
      (∀ g, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (L : Set Y)) ∧
      (∀ g, ρ g ∈ jBar L J) ∧
      ∃ v : ↥L ⧸ Subgroup.center ↥L, CentCycBar (jBar L J) p v := by
  classical
  have hJL : J ≤ L := h.parab.1
  obtain ⟨ρ, hρmk, hρker⟩ := exists_leviHom (L := L) (J := J) hJL
  have hcomm : ∀ a ∈ J, ∀ b ∈ Subgroup.centralizer (L : Set Y), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a (hJL ha)
  have hρJ : ∀ g : ↥(J ⊔ Subgroup.centralizer (L : Set Y)), ρ g ∈ jBar L J := by
    intro g
    obtain ⟨a, ha, c, hc, hg⟩ := exists_mul_of_mem_sup_commute hcomm g.2
    have hg' : g = ⟨a * c, Subgroup.mul_mem_sup ha hc⟩ := Subtype.ext hg
    rw [hg', hρmk a ha c hc]
    exact ⟨⟨a, hJL ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  set D' : Subgroup ↥(J ⊔ Subgroup.centralizer (L : Set Y)) := D.subgroupOf (J ⊔ Subgroup.centralizer (L : Set Y)) with hD'
  set Dh : Subgroup (↥L ⧸ Subgroup.center ↥L) := D'.map ρ with hDh
  have hD'map : D'.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype = D := Subgroup.map_subgroupOf_eq_of_le hDJ
  have hD'perf : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective (J ⊔ Subgroup.centralizer (L : Set Y)).subtype_injective
    rw [Subgroup.map_commutator, hD'map, hDp]
  have hDhperf : ⁅Dh, Dh⁆ = Dh := by
    rw [hDh, ← Subgroup.map_commutator, hD'perf]
  have hDhJ : Dh ≤ jBar L J := by
    rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  have hcardD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ).toEquiv
  have hD'mem : ∀ g : ↥(J ⊔ Subgroup.centralizer (L : Set Y)), g ∈ D' ↔ (g : Y) ∈ D := fun g => Subgroup.mem_subgroupOf
  have hD'cyc : ∀ A : Subgroup ↥(J ⊔ Subgroup.centralizer (L : Set Y)), A ≤ D' → IsPGroup p A → IsCyclic A := by
    intro A hA hAp
    have hAm : A.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype ≤ D := by
      rintro _ ⟨a, ha, rfl⟩
      exact (hD'mem a).1 (hA ha)
    have : IsCyclic ↥(A.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype) := hDcyc _ hAm (hAp.map (J ⊔ Subgroup.centralizer (L : Set Y)).subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective A (J ⊔ Subgroup.centralizer (L : Set Y)).subtype (J ⊔ Subgroup.centralizer (L : Set Y)).subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hD'cycG : ∀ A : Subgroup ↥D', IsPGroup p A → IsCyclic A := by
    intro A hAp
    have h1 : IsCyclic ↥(A.map D'.subtype) := hD'cyc _ (by
      rintro _ ⟨a, -, rfl⟩
      exact a.2) (hAp.map D'.subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective A D'.subtype D'.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hxM : x ∈ (J ⊔ Subgroup.centralizer (L : Set Y)) := hDJ hxD
  set xM : ↥(J ⊔ Subgroup.centralizer (L : Set Y)) := ⟨x, hxM⟩ with hxMdef
  have hxD' : xM ∈ D' := (hD'mem xM).2 hxD
  set x' : ↥D' := ⟨xM, hxD'⟩ with hx'def
  have hx'p : x' ^ p = 1 := Subtype.ext (Subtype.ext hxp)
  have hρx : ρ xM ≠ 1 := fun h1 => hxC ((hρker xM).1 h1)
  have hx'1 : x' ≠ 1 := fun h1 => hρx (by
    have : xM = 1 := congrArg (fun z : ↥D' => (z : ↥(J ⊔ Subgroup.centralizer (L : Set Y)))) h1
    rw [this, map_one])
  have hx'N : x' ∉ (ρ.subgroupMap D').ker := fun hk => hρx (by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    exact this)
  have hNp : ¬ p ∣ Nat.card (ρ.subgroupMap D').ker :=
    normal_pPrime_of_cycSylow hp hD'cycG hx'p hx'1 hx'N
  have hDhdvd : ∀ k, p ^ k ∣ Nat.card D → p ^ k ∣ Nat.card Dh := by
    intro k hk
    have hsurj : Function.Surjective (ρ.subgroupMap D') := ρ.subgroupMap_surjective D'
    have hmul := Subgroup.card_ker_mul_card_of_surjective hsurj
    have hcop : Nat.Coprime (p ^ k) (Nat.card (ρ.subgroupMap D').ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hNp)
    rw [← hcardD', ← hmul] at hk
    exact hcop.dvd_of_dvd_mul_left hk
  have hDhcyc : ∀ A ≤ Dh, IsPGroup p A → IsCyclic A := by
    intro A hADh hAp
    have hPmap : (D' ⊓ A.comap ρ).map ρ = A := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact hg.2
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hADh hy
        exact ⟨g, ⟨hg, hy⟩, rfl⟩
    obtain ⟨R, hRP, hRp, hRmap⟩ := exists_pSubgroup_map_eq hp hPmap hAp
    have hRcyc : IsCyclic R := hD'cyc R (fun r hr => (hRP hr).1) hRp
    subst hRmap
    have := hRcyc
    exact isCyclic_of_surjective (ρ.subgroupMap R) (ρ.subgroupMap_surjective R)
  set K : Subgroup (↥L ⧸ Subgroup.center ↥L) := perfectJoin (jBar L J) with hK
  have hDhK : Dh ≤ K := le_perfectJoin hDhJ hDhperf
  have hKdvd : ∀ k, p ^ k ∣ Nat.card K → p ^ k ∣ Nat.card Dh := by
    intro k hk
    obtain ⟨W, hWJ, hWp, hWmap⟩ := exists_perfect_lift_le h.parab (perfectJoin_perfect (jBar L J))
      (perfectJoin_le (jBar L J))
    have h1 : Nat.card K ∣ Nat.card (W.subgroupOf L) := by
      rw [hK, ← hWmap]
      exact Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective _ _)
    have h2 : Nat.card (W.subgroupOf L) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWJ.trans hJL)).toEquiv
    exact hDhdvd k (hDpart W hWJ hWp k (by rw [← h2]; exact hk.trans h1))
  have hKcyc := cyc_of_sylow_dvd_le hp hDhK hDhcyc hKdvd
  obtain ⟨l, hl, c, hc, hxlc⟩ := exists_mul_of_mem_sup_commute hcomm hxM
  have hxM' : xM = ⟨l * c, Subgroup.mul_mem_sup hl hc⟩ := Subtype.ext hxlc
  have hvdef : ρ xM = (QuotientGroup.mk ⟨l, hJL hl⟩ : ↥L ⧸ Subgroup.center ↥L) := by
    rw [hxM', hρmk l hl c hc]
  have hvDh : ρ xM ∈ Dh := ⟨xM, hxD', rfl⟩
  obtain ⟨S₀, hS₀, hne, htop⟩ := exists_sylow_parab_central h
  refine ⟨ρ, hρker, hρJ, ρ xM, ⟨⟨S₀, hS₀, hne⟩, htop, ?_, ?_, hρx, hDhK hvDh, ?_⟩⟩
  · intro V hVJ hV Q hQV hQp
    exact hKcyc Q (hQV.trans (le_perfectJoin hVJ hV)) hQp
  · rw [← map_pow]
    have : xM ^ p = 1 := Subtype.ext hxp
    rw [this, map_one]
  · intro V hVC hV
    rw [hvdef] at hVC
    exact perfect_cent_trivial_one (l := ⟨l, hJL hl⟩) (c := c) hc hxlc hxW hVC hV

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
