module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup


variable {J T : Type} [Group J] [Group T]

@[expose] def restrictK (π : J →* T) (K : Subgroup T) : ↥(K.comap π) →* ↥K :=
  (π.comp (K.comap π).subtype).codRestrict K (fun x => x.2)

theorem restrictK_coe (π : J →* T) (K : Subgroup T) (x : ↥(K.comap π)) :
    ((restrictK π K x : ↥K) : T) = π (x : J) := rfl

theorem restrictK_surjective (π : J →* T) (hπ : Function.Surjective π) (K : Subgroup T) :
    Function.Surjective (restrictK π K) := by
  intro k
  obtain ⟨g, hg⟩ := hπ (k : T)
  exact ⟨⟨g, by simp [mem_comap, hg]⟩, Subtype.ext hg⟩

theorem ker_restrictK_le_center (π : J →* T) (hz : π.ker ≤ center J) (K : Subgroup T) :
    (restrictK π K).ker ≤ center ↥(K.comap π) := by
  intro x hx
  have hx1 : π (x : J) = 1 := by
    have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [restrictK_coe] at h
    simpa using h
  have hxc : (x : J) ∈ center J := hz (MonoidHom.mem_ker.mpr hx1)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hxc g)

theorem card_comap_eq_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) (C : Subgroup B) :
    Nat.card (C.comap f) = Nat.card f.ker * Nat.card C := by
  have hB : Finite B := Finite.of_surjective f hf
  have h1 : Nat.card (C.comap f) * (C.comap f).index = Nat.card A := Subgroup.card_mul_index _
  have h2 : Nat.card C * C.index = Nat.card B := Subgroup.card_mul_index _
  have h3 : Nat.card f.ker * Nat.card B = Nat.card A := card_ker_mul_card_of_surjective hf
  have h4 : (C.comap f).index = C.index := Subgroup.index_comap_of_surjective C hf
  have hpos : 0 < C.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := C))
  rw [h4] at h1
  have : Nat.card (C.comap f) * C.index = (Nat.card f.ker * Nat.card C) * C.index := by
    rw [h1, ← h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem central_pow_index_mem_commutator {J : Type*} [Group J] [Finite J]
    (hJ : Group.IsPerfect J) {p : ℕ} [Fact p.Prime] (P : Sylow p J) {z : J}
    (hz : z ∈ Subgroup.center J) :
    z ^ (P : Subgroup J).index ∈ ⁅(P : Subgroup J), (P : Subgroup J)⁆ := by
  classical
  let H : Subgroup J := P
  have : H.FiniteIndex := inferInstance
  let ϕ : H →* Abelianization H := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : J), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center J := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hc
    have := hc g₀⁻¹
    calc g₀⁻¹ * z ^ k * g₀ = z ^ k * g₀⁻¹ * g₀ := by rw [this]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have h2 : MonoidHom.transfer ϕ z = 1 := by
    have hker : commutator J ≤ (MonoidHom.transfer ϕ).ker :=
      Abelianization.commutator_subset_ker _
    have : commutator J = ⊤ := hJ.commutator_eq_top
    rw [this] at hker
    exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top z))
  rw [h2] at h1
  have hmem : z ^ H.index ∈ H := MonoidHom.transfer_eq_pow_aux z key
  have h3 : (⟨z ^ H.index, hmem⟩ : H) ∈ commutator H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h3, rfl⟩

theorem central_mem_commutator_sylow {J : Type*} [Group J] [Finite J]
    (hJ : Group.IsPerfect J) {p : ℕ} [Fact p.Prime] (P : Sylow p J) {z : J}
    (hz : z ∈ Subgroup.center J) (hzp : ∃ n : ℕ, z ^ (p ^ n) = 1) :
    z ∈ ⁅(P : Subgroup J), (P : Subgroup J)⁆ := by
  classical
  obtain ⟨n, hn⟩ := hzp
  have hord : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
  have hzP : z ∈ (P : Subgroup J) := by
    have hnorm : (zpowers z).Normal :=
      normal_of_le_center ((Subgroup.zpowers_le).mpr hz)
    have hp : IsPGroup p (zpowers z) := by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).mp hord
      exact IsPGroup.of_card (by rw [Nat.card_zpowers]; exact hm)
    exact hp.le_sylow_of_normal P (Subgroup.mem_zpowers z)
  have hcop : Nat.Coprime (orderOf z) (P : Subgroup J).index := by
    refine Nat.Coprime.coprime_dvd_left hord ?_
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
      (Sylow.not_dvd_index P))
  have hpow := central_pow_index_mem_commutator hJ P hz
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ,
      (1 : ℤ) = (orderOf z : ℤ) * a + ((P : Subgroup J).index : ℤ) * b :=
    ⟨Nat.gcdA _ _, Nat.gcdB _ _, by
      have := Nat.gcd_eq_gcd_ab (orderOf z) (P : Subgroup J).index
      rw [hcop] at this
      simpa using this⟩
  have hz' : z = (z ^ (P : Subgroup J).index) ^ b := by
    calc z = z ^ (1 : ℤ) := (zpow_one z).symm
      _ = z ^ ((orderOf z : ℤ) * a + ((P : Subgroup J).index : ℤ) * b) := by rw [← hab]
      _ = (z ^ (P : Subgroup J).index) ^ b := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
          one_zpow, one_mul]
  rw [hz']
  exact Subgroup.zpow_mem _ hpow b

@[expose] def CoverBound (Q : Type) [Group Q] (p m : ℕ) : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ q : E →* Q,
    Function.Surjective q → q.ker ≤ center E → IsPGroup p q.ker → Nat.card q.ker ∣ m

theorem eq_one_of_mem_commutator_comap [Finite J] (π : J →* T) (hπ : Function.Surjective π)
    (hz : π.ker ≤ center J) {p : ℕ} [Fact p.Prime] (hp : IsPGroup p π.ker) (K : Subgroup T)
    (hK : Group.IsPerfect ↥K) {Q : Type} [Group Q] (e : ↥K ⧸ center ↥K ≃* Q)
    (hKp : IsPGroup p (center ↥K)) (hb : CoverBound Q p (Nat.card (center ↥K))) :
    ∀ z ∈ π.ker, z ∈ ⁅K.comap π, K.comap π⁆ → z = 1 := by
  classical
  have : Finite ↥(K.comap π) := inferInstance
  let f := restrictK π K
  have hfs := restrictK_surjective π hπ K
  have hfk := ker_restrictK_le_center π hz K
  have : Finite ↥K := Finite.of_surjective f hfs
  obtain ⟨-, hLperf, hlamsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective f hfs hfk hK
  let L : Subgroup ↥(K.comap π) := commutator ↥(K.comap π)
  let lam : ↥L →* ↥K := f.comp L.subtype
  have hlamk : lam.ker ≤ center ↥L := by
    intro x hx
    have hxc : (x : ↥(K.comap π)) ∈ center ↥(K.comap π) := hfk hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hxc (g : ↥(K.comap π))))
  have hcen : (center ↥K).comap lam = center ↥L :=
    CFSG.LocalCores.comap_center_eq_of_perfect hLperf lam hlamsurj hlamk
  let q : ↥L →* Q := e.toMonoidHom.comp ((QuotientGroup.mk' (center ↥K)).comp lam)
  have hqs : Function.Surjective q :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hlamsurj)
  have hqker : q.ker = center ↥L := by
    rw [← hcen]
    ext x
    simp only [q, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  have hpker : IsPGroup p lam.ker := by
    intro g
    obtain ⟨x, hx⟩ := g
    have hx1 : π ((x : ↥(K.comap π)) : J) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [lam, f, restrictK_coe] using h
    obtain ⟨k, hk⟩ := hp ⟨((x : ↥(K.comap π)) : J), hx1⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hcard : Nat.card (center ↥L) = Nat.card lam.ker * Nat.card (center ↥K) := by
    rw [← hcen]
    exact card_comap_eq_of_surjective lam hlamsurj (center ↥K)
  have hpC : IsPGroup p (center ↥L) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hpker
    obtain ⟨b, hb'⟩ := (IsPGroup.iff_card).mp hKp
    exact IsPGroup.of_card (n := a + b) (by rw [hcard, ha, hb', pow_add])
  have hdvd := hb ↥L hLperf q hqs hqker.le (hqker ▸ hpC)
  rw [hqker, hcard] at hdvd
  have hm : 0 < Nat.card (center ↥K) := Nat.card_pos
  have hle := Nat.le_of_dvd hm hdvd
  have hk1 : Nat.card lam.ker = 1 := by
    have h0 : 0 < Nat.card lam.ker := Nat.card_pos
    by_contra hne
    have : 2 ≤ Nat.card lam.ker := by omega
    nlinarith
  have hbot : lam.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hk1
  intro z hz1 hzL
  have hzπ : π z = 1 := MonoidHom.mem_ker.mp hz1
  have hzH : z ∈ K.comap π := by simp [mem_comap, hzπ]
  rw [← Subgroup.map_subtype_commutator] at hzL
  obtain ⟨x, hx, hxz⟩ := hzL
  have hxmem : (⟨x, hx⟩ : ↥L) ∈ lam.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show π (x : J) = 1
    have : (x : J) = z := hxz
    rw [this]
    exact hzπ
  rw [hbot, Subgroup.mem_bot] at hxmem
  have hx1 : x = 1 := congrArg Subtype.val hxmem
  rw [← hxz, hx1]
  rfl


theorem exists_sylow_le_comap [Finite J] (π : J →* T) (hπ : Function.Surjective π) {p : ℕ}
    [Fact p.Prime] (K : Subgroup T)
    (hfac : (Nat.card K).factorization p = (Nat.card T).factorization p) :
    ∃ P : Sylow p J, (P : Subgroup J) ≤ K.comap π := by
  classical
  have hT : Finite T := Finite.of_surjective π hπ
  have hHc : Nat.card (K.comap π) = Nat.card π.ker * Nat.card K :=
    card_comap_eq_of_surjective π hπ K
  have hJc : Nat.card π.ker * Nat.card T = Nat.card J := card_ker_mul_card_of_surjective hπ
  have hk0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hfH : (Nat.card (K.comap π)).factorization p = (Nat.card J).factorization p := by
    rw [hHc, ← hJc, Nat.factorization_mul hk0 hK0, Nat.factorization_mul hk0 hT0]
    simp [hfac]
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(K.comap π)) := inferInstance
  have hQc : Nat.card (Q : Subgroup ↥(K.comap π)) = p ^ (Nat.card (K.comap π)).factorization p :=
    Sylow.card_eq_multiplicity Q
  set Q' : Subgroup J := (Q : Subgroup ↥(K.comap π)).map (K.comap π).subtype with hQ'
  have hQ'c : Nat.card Q' = p ^ (Nat.card J).factorization p := by
    rw [hQ', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hQc, hfH]
  have hQ'p : IsPGroup p Q' := IsPGroup.of_card hQ'c
  obtain ⟨P, hP⟩ := hQ'p.exists_le_sylow
  have hPc : Nat.card (P : Subgroup J) = p ^ (Nat.card J).factorization p :=
    Sylow.card_eq_multiplicity P
  have hPQ : (P : Subgroup J) = Q' :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [hPc, hQ'c])).symm
  exact ⟨P, by rw [hPQ]; exact Subgroup.map_subtype_le _⟩

theorem ker_eq_bot_of_local [Finite J] (π : J →* T) (hπ : Function.Surjective π)
    (hJ : Group.IsPerfect J) (hz : π.ker ≤ center J) {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p π.ker) (K : Subgroup T)
    (hfac : (Nat.card K).factorization p = (Nat.card T).factorization p)
    (hA : ∀ z ∈ π.ker, z ∈ ⁅K.comap π, K.comap π⁆ → z = 1) : π.ker = ⊥ := by
  obtain ⟨P, hP⟩ := exists_sylow_le_comap π hπ K hfac
  rw [eq_bot_iff]
  intro z hzk
  obtain ⟨k, hk⟩ := hp ⟨z, hzk⟩
  have hzp : ∃ n : ℕ, z ^ (p ^ n) = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
  have h1 := central_mem_commutator_sylow hJ P (hz hzk) hzp
  have h2 : z ∈ ⁅K.comap π, K.comap π⁆ := Subgroup.commutator_mono hP hP h1
  exact Subgroup.mem_bot.mpr (hA z hzk h2)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
