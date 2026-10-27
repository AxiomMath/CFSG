module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShape3Basic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Roots

public section

namespace CFSG.OddStandard.AltStdCycTwo.Shape3

open Subgroup Equiv Equiv.Perm
open AltStdBal (Cyc rho rho_eq_one_iff rho_of_mem eq_one_or_eq_of_card_eq_two)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] noncomputable def rhoR (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (R : Subgroup G) (hRC : R ≤ centralizer ({z} : Set G)) :
    R →* Perm (Fin n) :=
  (rho θ hn).comp (Subgroup.inclusion (hRC.trans (cent_le_normalizer hS d)))

theorem rhoR_apply (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (d : Cyc L Q z) {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (r : R) :
    rhoR hS θ hn d R hRC r = rho θ hn ⟨r, cent_le_normalizer hS d (hRC r.2)⟩ :=
  rfl

theorem rhoR_ker_card (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R) (hzR : z ∈ R) :
    Nat.card (rhoR hS θ hn d R hRC).ker = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := by
    intro h1
    have := d.order
    rw [h1, orderOf_one] at this
    omega
  have hkerz : (⟨z, hzR⟩ : R) ∈ (rhoR hS θ hn d R hRC).ker := by
    rw [MonoidHom.mem_ker, rhoR_apply]
    exact (rho_eq_one_iff θ hn _).2 (d.le d.mem)
  rw [Nat.card_eq_two_iff' (1 : (rhoR hS θ hn d R hRC).ker)]
  refine ⟨⟨⟨z, hzR⟩, hkerz⟩, ?_, ?_⟩
  · intro h1
    have := congrArg (fun y : (rhoR hS θ hn d R hRC).ker => ((y : R) : G)) h1
    exact hz1 (by simpa using this)
  · intro y hy
    have hy1 : rhoR hS θ hn d R hRC y = 1 := y.2
    rw [rhoR_apply] at hy1
    have hyK := (rho_eq_one_iff θ hn _).1 hy1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR (y : R)
    have hyk : ((y : R) : G) ^ 2 ^ k = 1 := by
      rw [← hk, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    have hyQ : ((y : R) : G) ∈ Q :=
      zpowers_le.2 d.mem (mem_zpowers_of_two_pow d hQ2 ⟨hyK, hRC (y : R).2⟩ hyk)
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hyQ with h2 | h2
    · exfalso
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      simpa using h2
    · apply Subtype.ext
      apply Subtype.ext
      simpa using h2

theorem sign_rhoR_eq_neg_one_iff (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G))
    (r : R) :
    sign (rhoR hS θ hn d R hRC r) = -1 ↔ (r : G) ∉ L ⊔ centralizer (L : Set G) := by
  have hrN := cent_le_normalizer hS d (hRC r.2)
  rw [rhoR_apply]
  constructor
  · intro hs hmem
    rw [sign_rho_eq_one θ hn hrN hmem] at hs
    exact absurd hs (by decide)
  · exact sign_rho_eq_neg_one θ hn hrN

theorem sq_eq_iff (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G} (hu : u ∈ centralizer ({z} : Set G))
    (huO : u ∉ L ⊔ centralizer (L : Set G)) (hu2 : u ^ 2 = z)
    {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R) (w : L)
    (r : R) :
    (r : G) ^ 2 = z * (w : G) ↔
      (sign (rhoR hS θ hn d R hRC r) = -1 ∧
        (rhoR hS θ hn d R hRC r) ^ 2 = ((θ w : alternatingGroup (Fin n)) : Perm (Fin n))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN := cent_le_normalizer hS d
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR r
  have hrk : (r : G) ^ 2 ^ k = 1 := by
    rw [← hk, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hzN : z ∈ normalizer (L : Set G) := hCN hzC
  have hρz : rho θ hn ⟨z, hzN⟩ = 1 := (rho_eq_one_iff θ hn _).2 (d.le d.mem)
  have hwN : (w : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer w.2
  have hρw : rho θ hn ⟨(w : G), hwN⟩ = ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)) :=
    rho_of_mem θ hn w hwN
  have hrN : (r : G) ∈ normalizer (L : Set G) := hCN (hRC r.2)
  have hsq : (rhoR hS θ hn d R hRC r) ^ 2 = rho θ hn ⟨(r : G) * (r : G), mul_mem hrN hrN⟩ := by
    rw [sq, ← map_mul]
    rfl
  constructor
  · intro hr2
    have hrO : (r : G) ∉ L ⊔ centralizer (L : Set G) := by
      intro hmem
      obtain ⟨l, hl, q, hq, hlq⟩ := exists_mul_of_two_pow hS θ hn d hQ2 (hRC r.2) hmem hrk
      have hmem' : (r : G) ∈ L ⊔ Q := by
        rw [← hlq]
        exact mul_mem_sup hl hq
      have h1 := AltStdSec.sq_mem_L_of_mem_sup d hQ2 hmem'
      rw [hr2] at h1
      apply z_not_mem_L θ hn d
      have : z = (z * (w : G)) * (w : G)⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem w.2)
    refine ⟨(sign_rhoR_eq_neg_one_iff hS θ hn d hRC r).2 hrO, ?_⟩
    rw [hsq]
    have h2 : (⟨(r : G) * (r : G), mul_mem hrN hrN⟩ : normalizer (L : Set G)) =
        ⟨z, hzN⟩ * ⟨(w : G), hwN⟩ := Subtype.ext (by
          have h7 := hr2
          rw [sq] at h7
          exact h7)
    rw [h2, map_mul, hρz, hρw, one_mul]
  · rintro ⟨hs, hsq2⟩
    have hrO := (sign_rhoR_eq_neg_one_iff hS θ hn d hRC r).1 hs
    obtain ⟨l, hl, hrr⟩ := exists_sq_eq_mul hS θ hn d hQ2 hu huO hu2 (hRC r.2) hrO hrk
    have hlN : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
    have h3 : rho θ hn ⟨l, hlN⟩ = ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
      rho_of_mem θ hn ⟨l, hl⟩ hlN
    have h4 : (⟨(r : G) * (r : G), mul_mem hrN hrN⟩ : normalizer (L : Set G)) =
        ⟨z, hzN⟩ * ⟨l, hlN⟩ := Subtype.ext hrr
    rw [hsq, h4, map_mul, hρz, one_mul, h3] at hsq2
    have h5 : (⟨l, hl⟩ : L) = w := θ.injective (Subtype.ext hsq2)
    have h6 : l = (w : G) := congrArg Subtype.val h5
    rw [sq, hrr, h6]

theorem card_roots_eq_two_mul (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huO : u ∉ L ⊔ centralizer (L : Set G))
    (hu2 : u ^ 2 = z) {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G))
    (hR : IsPGroup 2 R) (hzR : z ∈ R) (w : L) :
    Nat.card {r : R // (r : G) ^ 2 = z * (w : G)} =
      2 * Nat.card {s : (rhoR hS θ hn d R hRC).range //
        sign (s : Perm (Fin n)) = -1 ∧
          (s : Perm (Fin n)) ^ 2 = ((θ w : alternatingGroup (Fin n)) : Perm (Fin n))} := by
  have hπ : Function.Surjective (rhoR hS θ hn d R hRC).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have key := AltStdSec.card_subtype_comp (rhoR hS θ hn d R hRC).rangeRestrict hπ
    (fun s => sign (s : Perm (Fin n)) = -1 ∧
      (s : Perm (Fin n)) ^ 2 = ((θ w : alternatingGroup (Fin n)) : Perm (Fin n)))
  rw [MonoidHom.ker_rangeRestrict, rhoR_ker_card hS θ hn d hQ2 hRC hR hzR] at key
  rw [← key]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight (fun r => sq_eq_iff hS θ hn d hQ2 hu huO hu2 hRC hR w r))

theorem rhoC_surjective (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) {u : G} (hu : u ∈ centralizer ({z} : Set G))
    (huO : u ∉ L ⊔ centralizer (L : Set G)) :
    Function.Surjective (rhoR hS θ hn d (centralizer ({z} : Set G)) le_rfl) := by
  intro σ
  have hsu : sign (rhoR hS θ hn d (centralizer ({z} : Set G)) le_rfl ⟨u, hu⟩) = -1 :=
    (sign_rhoR_eq_neg_one_iff hS θ hn d le_rfl ⟨u, hu⟩).2 huO
  have heven : ∀ τ : Perm (Fin n), sign τ = 1 →
      ∃ c : centralizer ({z} : Set G),
        rhoR hS θ hn d (centralizer ({z} : Set G)) le_rfl c = τ := by
    intro τ hτ
    have hmem : τ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.2 hτ
    let l : L := θ.symm ⟨τ, hmem⟩
    refine ⟨⟨l, le_cent_single hS d l.2⟩, ?_⟩
    rw [rhoR_apply, rho_of_mem θ hn l (cent_le_normalizer hS d (le_cent_single hS d l.2))]
    simp [l]
  rcases Int.units_eq_one_or (sign σ) with hs | hs
  · exact heven σ hs
  · obtain ⟨c, hc⟩ := heven ((rhoR hS θ hn d (centralizer ({z} : Set G)) le_rfl ⟨u, hu⟩)⁻¹ * σ)
      (by rw [map_mul, map_inv, hsu, hs]; decide)
    refine ⟨⟨u, hu⟩ * c, ?_⟩
    rw [map_mul, hc]
    group

theorem range_rhoR_maximal (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) {u : G} (hu : u ∈ centralizer ({z} : Set G))
    (huO : u ∉ L ⊔ centralizer (L : Set G)) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) :
    IsPGroup 2 (rhoR hS θ hn d R hRC).range ∧
      ∀ P' : Subgroup (Perm (Fin n)), IsPGroup 2 P' → (rhoR hS θ hn d R hRC).range ≤ P' →
        P' = (rhoR hS θ hn d R hRC).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hR.of_surjective _ (MonoidHom.rangeRestrict_surjective _), ?_⟩
  intro P' hP' hle
  set C := centralizer ({z} : Set G) with hC
  set H : Subgroup G := (P'.comap (rhoR hS θ hn d C le_rfl)).map C.subtype with hH
  have hHC : H ≤ C := Subgroup.map_subtype_le _
  have hRH : R ≤ H := by
    intro r hr
    refine ⟨⟨r, hRC hr⟩, ?_, rfl⟩
    show rhoR hS θ hn d C le_rfl ⟨r, hRC hr⟩ ∈ P'
    exact hle ⟨⟨r, hr⟩, rfl⟩
  have hrange : (rhoR hS θ hn d H hHC).range = P' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 x.2
      have h1 : rhoR hS θ hn d H hHC x = rhoR hS θ hn d C le_rfl c := by
        rw [rhoR_apply, rhoR_apply]
        exact congrArg (rho θ hn) (Subtype.ext hcx.symm)
      rw [h1]
      exact hc
    · intro s hs
      obtain ⟨c, hc⟩ := rhoC_surjective hS θ hn d hu huO s
      have hcH : (c : G) ∈ H := ⟨c, by
        show rhoR hS θ hn d C le_rfl c ∈ P'
        rw [hc]
        exact hs, rfl⟩
      exact ⟨⟨c, hcH⟩, hc⟩
  have hRp : IsPGroup 2 (R.subgroupOf H) := hR.of_equiv (subgroupOfEquivOfLe hRH).symm
  obtain ⟨T, hRT⟩ := hRp.exists_le_sylow
  have hTR : (T : Subgroup H).map H.subtype = R := by
    refine hRmax _ ((Subgroup.map_subtype_le _).trans hHC) (T.isPGroup'.map _) ?_
    intro r hr
    exact ⟨⟨r, hRH hr⟩, hRT (Subgroup.mem_subgroupOf.2 hr), rfl⟩
  set f := rhoR hS θ hn d H hHC with hf
  have hp : IsPGroup 2 (⊤ : Subgroup f.range) := by
    have h1 : IsPGroup 2 f.range := by
      rw [hrange]
      exact hP'
    exact h1.to_subgroup ⊤
  have htop : (T : Subgroup H).map f.rangeRestrict = ⊤ := by
    have h1 := (T.mapSurjective (MonoidHom.rangeRestrict_surjective f)).is_maximal' hp le_top
    exact h1.symm
  refine le_antisymm ?_ hle
  intro s hs
  have hs' : s ∈ f.range := by
    rw [hrange]
    exact hs
  have hsT : (⟨s, hs'⟩ : f.range) ∈ (T : Subgroup H).map f.rangeRestrict := by
    rw [htop]
    trivial
  obtain ⟨t, htT, hts⟩ := Subgroup.mem_map.1 hsT
  have htR : (t : G) ∈ R := by
    rw [← hTR]
    exact ⟨t, htT, rfl⟩
  exact ⟨⟨t, htR⟩, congrArg Subtype.val hts⟩

end CFSG.OddStandard.AltStdCycTwo.Shape3
