module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Aux

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

section CaseB

theorem mem_sylow_of_normal {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (S : Sylow r G) [S.Normal] {g : G} (hg : ∃ n : ℕ, g ^ r ^ n = 1) : g ∈ S := by
  have hH : IsPGroup r ↥(Subgroup.zpowers g) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn⟩ := hg
    refine ⟨n, Subtype.ext ?_⟩
    show (g ^ m) ^ r ^ n = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S S'
  rw [← hx, Sylow.smul_eq_of_normal] at hS'
  exact hS' (Subgroup.mem_zpowers g)

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let c : ↥H → ↥H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hinj : Function.Injective c := by
    intro y z hyz
    apply Subtype.ext
    have := congrArg Subtype.val hyz
    simpa [c] using this
  obtain ⟨x', hx'⟩ := Finite.surjective_of_injective hinj ⟨g * x * g⁻¹, hx⟩
  have h1 : (x' : G) = x := by
    have := congrArg Subtype.val hx'
    simpa [c] using this
  rw [← h1]
  exact x'.2

end CaseB

section CaseBFrame

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} [K.Normal] {a : Γ} {P : Subgroup Γ}

theorem Mod55.actYHom_eq_of_invariant (hf : Mod55 p ρ K a P) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) {Q : Subgroup (K ⧸ center ↥K)} (hQ : IsPGroup r ↥Q)
    (hinv : ∀ y ∈ Q, actYHom (K := K) a y ∈ Q) {y : K ⧸ center ↥K} (hy : y ∈ Q) :
    actYHom (K := K) a y = y := by
  have : Fact r.Prime := ⟨hr⟩
  let π : ↥K →* K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  let T : Subgroup ↥K := Q.comap π
  let f : ↥T →* ↥Q := (π.comp T.subtype).codRestrict Q (fun t => t.2)
  have hker : f.ker ≤ center ↥T := by
    intro t ht
    have h1 : π (t : ↥K) = 1 := by
      have := congrArg (fun z : ↥Q => (z : K ⧸ center ↥K)) (MonoidHom.mem_ker.mp ht)
      exact this
    have h2 : (t : ↥K) ∈ center ↥K := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp h2 (g : ↥K)
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have : Group.IsNilpotent ↥T := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨Sy⟩ : Nonempty (Sylow r ↥T) := inferInstance
  let ι : ↥T →* Γ := K.subtype.comp T.subtype
  let Qt : Subgroup Γ := (Sy : Subgroup ↥T).map ι
  have hQt : IsPGroup r ↥Qt := Sy.isPGroup'.map ι
  have hconj : ∀ x ∈ Qt, a * x * a⁻¹ ∈ Qt := by
    rintro _ ⟨s, hs, rfl⟩
    set k : ↥K := (s : ↥K) with hk
    have hπk : π k ∈ Q := s.2
    have hk' : π (MulAut.conjNormal a k : ↥K) ∈ Q := by
      have : π (MulAut.conjNormal a k : ↥K) = actYHom (K := K) a (π k) := rfl
      rw [this]
      exact hinv _ hπk
    obtain ⟨n, hn⟩ := Sy.isPGroup' ⟨s, hs⟩
    have hsn : s ^ r ^ n = 1 := congrArg Subtype.val hn
    have hkn : k ^ r ^ n = 1 := by
      have := congrArg (fun t : ↥T => (t : ↥K)) hsn
      simpa [hk] using this
    have hmem : (⟨MulAut.conjNormal a k, hk'⟩ : ↥T) ∈ Sy := by
      refine mem_sylow_of_normal Sy ⟨n, ?_⟩
      apply Subtype.ext
      show (MulAut.conjNormal a k) ^ r ^ n = 1
      rw [← map_pow, hkn, map_one]
    refine ⟨_, hmem, ?_⟩
    show ((MulAut.conjNormal a k : ↥K) : Γ) = a * (s : Γ) * a⁻¹
    rw [MulAut.conjNormal_apply]
  have hnorm : a ∈ normalizer (Qt : Set Γ) := mem_normalizer_of_conj_le hconj
  have hcentr := hf.centralizes_odd hr hr2 hrp hQt hnorm
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨k0, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨⟨k0, hz⟩, Subtype.ext rfl⟩
  have hmap : (Sy : Subgroup ↥T).map f = ⊤ := by
    have hdvd : ((Sy : Subgroup ↥T).map f).index ∣ (Sy : Subgroup ↥T).index :=
      Subgroup.index_map_dvd (Sy : Subgroup ↥T) hfs
    have hndvd : ¬ r ∣ (Sy : Subgroup ↥T).index := Sylow.not_dvd_index Sy
    obtain ⟨n, hn⟩ := hQ.index ((Sy : Subgroup ↥T).map f)
    have hn0 : n = 0 := by
      by_contra hne
      exact hndvd ((dvd_pow_self r hne).trans (hn ▸ hdvd))
    rw [hn0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  have hyT : (⟨y, hy⟩ : ↥Q) ∈ (Sy : Subgroup ↥T).map f := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hfs'⟩ := hyT
  have hπs : π (s : ↥K) = y := congrArg Subtype.val hfs'
  have hxQt : ((s : ↥K) : Γ) ∈ Qt := ⟨s, hs, rfl⟩
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hcentr hxQt)
  rw [← hπs]
  show π (MulAut.conjNormal a (s : ↥K) : ↥K) = π (s : ↥K)
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  calc a * ((s : ↥K) : Γ) * a⁻¹ = (((s : ↥K) : Γ) * a) * a⁻¹ := by rw [hcomm.symm]
    _ = ((s : ↥K) : Γ) := by group

end CaseBFrame

section Fixed

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} [K.Normal] {a : Γ} {P R : Subgroup Γ}

omit [Module.Finite (ZMod p) V] in
theorem Frame55.exists_sylow_fixed (hf : Frame55 k p ρ K a P R)
    (hU : innerPart (K := K) P = ⊥) :
    ∃ S : Sylow 2 (K ⧸ center ↥K), ∀ s ∈ S, actYHom (K := K) a s = s := by
  obtain ⟨Q, hQ⟩ := hf.sylow
  let π : ↥K →* K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨Q.mapSurjective hπ, ?_⟩
  intro s hs
  have hs' : s ∈ (Q : Subgroup ↥K).map π := by
    rw [← Sylow.coe_mapSurjective hπ Q]
    exact hs
  obtain ⟨q, hq, rfl⟩ := hs'
  have hqRK : (q : Γ) ∈ R ⊓ K := by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hc := comm_inf_le hf.normal hf.norm hqRK hf.a_mem
  set c : Γ := (q : Γ) * a * (q : Γ)⁻¹ * a⁻¹ with hcdef
  have hcU : (QuotientGroup.mk (⟨c, hc.2⟩ : ↥K) : K ⧸ center ↥K) ∈ innerPart (K := K) P :=
    mem_innerPart.mpr ⟨c, hc.1, actYHom_of_mem hc.2⟩
  rw [hU, Subgroup.mem_bot] at hcU
  show π (MulAut.conjNormal a q : ↥K) = π q
  have hq' : (MulAut.conjNormal a q : ↥K) = (⟨c, hc.2⟩ : ↥K)⁻¹ * q := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show a * (q : Γ) * a⁻¹ = c⁻¹ * (q : Γ)
    rw [hcdef]
    group
  rw [hq', map_mul, map_inv]
  have h1 : π (⟨c, hc.2⟩ : ↥K) = 1 := hcU
  rw [h1, inv_one, one_mul]

end Fixed

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
