module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

private lemma conjSub_mul (c d : G) (Y : Subgroup G) :
    conjSub (c * d) Y = conjSub c (conjSub d Y) := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private lemma mul_comm_of_mem_closure_pair {a b : G} (hab : a * b = b * a) {x y : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G))
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) : x * y = y * x := by
  have hcen : Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> simp [hab]
    | one => rw [one_mul, mul_one]
    | mul v w _ _ hv hw => rw [mul_assoc, hw, ← mul_assoc, hv, mul_assoc]
    | inv v _ hv =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hv, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.mem_centralizer_iff.mp (hcen hy) x hx

private lemma isPGroup_closure_pair_of_pow {p : ℕ} {a b : G} (hab : a * b = b * a) {k : ℕ}
    (ha : a ^ (p ^ k) = 1) (hb : b ^ (p ^ k) = 1) :
    IsPGroup p (Subgroup.closure ({a, b} : Set G)) := by
  have hpow : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ (p ^ k) = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl <;> assumption
    | one => exact one_pow _
    | mul v w hv' hw' hv hw =>
      rw [Commute.mul_pow (mul_comm_of_mem_closure_pair hab hv' hw'), hv, hw, one_mul]
    | inv v _ hv => rw [inv_pow, hv, inv_one]
  intro x
  exact ⟨k, Subtype.ext (by simpa using hpow x x.2)⟩

private lemma isSylowIn_conjSub {p : ℕ} {V P : Subgroup G} {c : G}
    (hP : IsSylowIn p V P) (hc : c ∈ Subgroup.normalizer (V : Set G)) :
    IsSylowIn p V (conjSub c P) := by
  have hcV : V.map (MulAut.conj c).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
  refine ⟨?_, hP.2.1.map _, ?_⟩
  · rw [conjSub, ← hcV]
    exact Subgroup.map_mono hP.1
  · rw [conjSub, ← hcV,
      Subgroup.relIndex_map_map_of_injective P V (MulAut.conj c).injective]
    exact hP.2.2

private lemma exists_conjSub_eq_of_isSylowIn {p : ℕ} [Fact p.Prime] [Finite G]
    {V P P' : Subgroup G} (hP : IsSylowIn p V P) (hP' : IsSylowIn p V P') :
    ∃ v ∈ V, conjSub v P = P' := by
  have hPidx : ¬ p ∣ (P.subgroupOf V).index := hP.2.2
  have hP'idx : ¬ p ∣ (P'.subgroupOf V).index := hP'.2.2
  let S : Sylow p ↥V := (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).toSylow hPidx
  let S' : Sylow p ↥V := (hP'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP'.1).symm).toSylow hP'idx
  haveI : Finite (Sylow p ↥V) :=
    Finite.of_injective (fun S : Sylow p ↥V => (S : Set ↥V))
      (fun S T h => Sylow.ext (by ext x; exact Set.ext_iff.mp h x))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥V S S'
  have hsub : (S : Subgroup ↥V).map (MulAut.conj (g : ↥V)).toMonoidHom = (S' : Subgroup ↥V) := by
    have h := congrArg (fun S : Sylow p ↥V => (S : Subgroup ↥V)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h using 2
    ext x
    rfl
  have hS : (S : Subgroup ↥V) = P.subgroupOf V := IsPGroup.toSylow_coe _ _
  have hS' : (S' : Subgroup ↥V) = P'.subgroupOf V := IsPGroup.toSylow_coe _ _
  have hleft : ((S : Subgroup ↥V).map (MulAut.conj (g : ↥V)).toMonoidHom).map V.subtype =
      conjSub (g : G) P := by
    rw [Subgroup.map_map]
    have hcomp : V.subtype.comp (MulAut.conj (g : ↥V)).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp V.subtype := by ext x; rfl
    rw [hcomp, ← Subgroup.map_map, hS, Subgroup.map_subgroupOf_eq_of_le hP.1, conjSub]
  refine ⟨(g : G), g.2, ?_⟩
  calc conjSub (g : G) P
      = ((S : Subgroup ↥V).map (MulAut.conj (g : ↥V)).toMonoidHom).map V.subtype := hleft.symm
    _ = (S' : Subgroup ↥V).map V.subtype := by rw [hsub]
    _ = P' := by rw [hS', Subgroup.map_subgroupOf_eq_of_le hP'.1]

private lemma sylow_decomp_of_surjective {H : Type*} [Group H] [Finite G] {r : ℕ} [Fact r.Prime]
    {M K0 Q : Subgroup G} (π : ↥K0 →* H) (hπ : Function.Surjective π)
    (hker : π.ker = M.subgroupOf K0) (hr : IsPGroup r H) (hQ : IsSylowIn r K0 Q) :
    ∀ x ∈ K0, ∃ m ∈ M, ∃ q ∈ Q, x = m * q := by
  intro x hx
  have hQsub : IsPGroup r (Q.subgroupOf K0) := hQ.2.1.comap_subtype
  have hQidx : ¬ r ∣ (Q.subgroupOf K0).index := hQ.2.2
  let S : Sylow r ↥K0 := hQsub.toSylow hQidx
  have hScoe : (S : Subgroup ↥K0) = Q.subgroupOf K0 := IsPGroup.toSylow_coe _ _
  have htop : ((S.mapSurjective hπ : Sylow r H) : Subgroup H) = ⊤ :=
    ((S.mapSurjective hπ).3 (hr.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hSmap : (S : Subgroup ↥K0).map π = ⊤ := by
    rw [← Sylow.coe_mapSurjective (hf := hπ) S]; exact htop
  have hxmem : π ⟨x, hx⟩ ∈ (S : Subgroup ↥K0).map π := by rw [hSmap]; exact Subgroup.mem_top _
  obtain ⟨q, hqS, hqeq⟩ := Subgroup.mem_map.mp hxmem
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp (by rw [← hScoe]; exact hqS)
  have hker_mem : q * ⟨x, hx⟩⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqeq, mul_inv_cancel]
  rw [hker] at hker_mem
  have hm : (((q * ⟨x, hx⟩⁻¹ : ↥K0)) : G) ∈ M := Subgroup.mem_subgroupOf.mp hker_mem
  refine ⟨(((q * ⟨x, hx⟩⁻¹ : ↥K0)) : G)⁻¹, inv_mem hm, (q : G), hqQ, ?_⟩
  have hcoe : (((q * ⟨x, hx⟩⁻¹ : ↥K0)) : G) = (q : G) * x⁻¹ := by
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]; group

end Helpers

theorem y7c_odd_Q {G : Type} [Group G] [Finite G] (M K : Subgroup G) (t g₀ : G) (r : ℕ)
    [Fact r.Prime] (hr2 : r ≠ 2)
    (hM2 : ∀ m ∈ M, m ^ 2 = 1) (hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hMK : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) (hMle : M ≤ K)
    (ht2 : t ^ 2 = 1) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hI : ∀ m ∈ M, t * m * t⁻¹ = m → ∃ u ∈ M, m * t = u * t * u⁻¹)
    (hg₀K : g₀ ∈ K) (hg₀c : ∀ k ∈ K, ⁅k, g₀⁆ ∈ M) (hg₀r : ∃ a : ℕ, g₀ ^ (r ^ a) ∈ M)
    (hg₀f : ∀ m ∈ M, g₀ * m * g₀⁻¹ = m → m = 1) :
    ∃ K0 Q : Subgroup G, M ≤ K0 ∧ K0 ≤ K ∧ (∀ k ∈ K, ∀ x ∈ K0, k * x * k⁻¹ ∈ K0) ∧
      (∀ x ∈ K0, ∀ k ∈ K, ⁅k, x⁆ ∈ M) ∧ (∀ x ∈ K0, ∃ m ∈ M, ∃ q ∈ Q, x = m * q) ∧
      IsSylowIn r K0 Q ∧ (∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      (∀ m ∈ M, (∀ q ∈ Q, q * m * q⁻¹ = m) → m = 1) ∧ (∀ x ∈ Q, x ∈ M → x = 1) := by
  classical
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact ht2
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hM2p : IsPGroup 2 M := fun m =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hM2 m m.2)⟩
  let g₁ : G := t * g₀ * t⁻¹
  let C : Subgroup G := Subgroup.closure ({g₀, g₁} : Set G)
  let K0 : Subgroup G := M ⊔ C
  have hg₁K : g₁ ∈ K := htK g₀ hg₀K
  have hMleK0 : M ≤ K0 := (le_sup_left : M ≤ M ⊔ C)
  have hg₀K0 : g₀ ∈ K0 := (le_sup_right : C ≤ M ⊔ C) (Subgroup.subset_closure (by simp))
  have hg₁K0 : g₁ ∈ K0 := (le_sup_right : C ≤ M ⊔ C) (Subgroup.subset_closure (by simp))
  let Z : Subgroup G :=
    { carrier := {x | x ∈ K ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ M}
      mul_mem' := by
        rintro x y ⟨hxK, hx⟩ ⟨hyK, hy⟩
        refine ⟨mul_mem hxK hyK, fun k hk => ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : x * ⁅k, y⁆ * x⁻¹ ∈ M := hMK x hxK (⁅k, y⁆) (hy k hk)
        have h2 : ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) ∈ M := mul_mem (hx k hk) h1
        simpa only [mul_assoc] using h2
      one_mem' := ⟨one_mem K, fun k hk => by simp⟩
      inv_mem' := by
        rintro x ⟨hxK, hx⟩
        refine ⟨inv_mem hxK, fun k hk => ?_⟩
        have hxk : ⁅x, k⁆ ∈ M := by
          rw [← commutatorElement_inv (g₁ := k) (g₂ := x)]
          exact inv_mem (hx k hk)
        rw [commutatorElement_inv_right]
        simpa using hMK x⁻¹ (inv_mem hxK) ⁅x, k⁆ hxk }
  have hMZ : M ≤ Z := fun m hm => ⟨hMle hm, fun k hk => by
    rw [commutatorElement_def]; exact mul_mem (hMK k hk m hm) (inv_mem hm)⟩
  have hg₀Z : g₀ ∈ Z := ⟨hg₀K, hg₀c⟩
  have hg₁Z : g₁ ∈ Z := by
    refine ⟨hg₁K, fun k hk => ?_⟩
    have hkt : t⁻¹ * k * t ∈ K := by simpa [htinv] using htK k hk
    have hconj : t * ⁅t⁻¹ * k * t, g₀⁆ * t⁻¹ = ⁅k, g₁⁆ := by
      rw [conjugate_commutatorElement, show t * (t⁻¹ * k * t) * t⁻¹ = k by group]
    rw [← hconj]
    exact htM _ (hg₀c _ hkt)
  have hCZ : C ≤ Z := by
    change Subgroup.closure ({g₀, g₁} : Set G) ≤ Z
    rw [Subgroup.closure_le]
    rintro x (hx | hx) <;> rw [hx] <;> assumption
  have hK0Z : K0 ≤ Z := sup_le hMZ hCZ
  have hK0K : K0 ≤ K := fun x hx => (hK0Z hx).1
  have hcentK0 : ∀ x ∈ K0, ∀ k ∈ K, ⁅k, x⁆ ∈ M := fun x hx k hk => (hK0Z hx).2 k hk
  have hK0norm : ∀ k ∈ K, ∀ x ∈ K0, k * x * k⁻¹ ∈ K0 := by
    intro k hk x hx
    have hcx : ⁅k, x⁆ ∈ M := hcentK0 x hx k hk
    have hkx : k * x * k⁻¹ = ⁅k, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [hkx]
    exact mul_mem ((le_sup_left : M ≤ M ⊔ C) hcx) hx
  have hK0nM : K0 ≤ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.le_normalizer_iff]; exact fun x hx m hm => hMK x (hK0K hx) m hm
  let N : Subgroup ↥K0 := M.subgroupOf K0
  haveI hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMleK0).mpr hK0nM
  let π : ↥K0 →* ↥K0 ⧸ N := QuotientGroup.mk' N
  let a : ↥K0 ⧸ N := π ⟨g₀, hg₀K0⟩
  let b : ↥K0 ⧸ N := π ⟨g₁, hg₁K0⟩
  obtain ⟨k, hk⟩ := hg₀r
  have hg₁pow : g₁ ^ (r ^ k) ∈ M := by
    rw [show g₁ = MulAut.conj t g₀ by simp [g₁, MulAut.conj_apply], ← map_pow]
    simpa [MulAut.conj_apply] using htM _ hk
  have ha_pow : a ^ (r ^ k) = 1 := by
    show π ⟨g₀, hg₀K0⟩ ^ (r ^ k) = 1
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    simpa using hk
  have hb_pow : b ^ (r ^ k) = 1 := by
    show π ⟨g₁, hg₁K0⟩ ^ (r ^ k) = 1
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    simpa using hg₁pow
  have hcomm_g : ⁅g₀, g₁⁆ ∈ M := by
    rw [← commutatorElement_inv (g₁ := g₁) (g₂ := g₀)]
    exact inv_mem (hg₀c g₁ hg₁K)
  have hab : a * b = b * a := by
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← map_commutatorElement π ⟨g₀, hg₀K0⟩ ⟨g₁, hg₁K0⟩,
      ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hcomm_g
  have hCsub : C.subgroupOf K0 =
      Subgroup.closure ({⟨g₀, hg₀K0⟩, ⟨g₁, hg₁K0⟩} : Set ↥K0) := by
    have hmap : (Subgroup.closure ({⟨g₀, hg₀K0⟩, ⟨g₁, hg₁K0⟩} : Set ↥K0)).map K0.subtype = C := by
      change (Subgroup.closure _).map K0.subtype = Subgroup.closure ({g₀, g₁} : Set G)
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨y, (hy | hy), rfl⟩ <;> (rw [hy]; simp)
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact ⟨⟨g₀, hg₀K0⟩, by simp, hx.symm⟩
        · exact ⟨⟨g₁, hg₁K0⟩, by simp, hx.symm⟩
    rw [Subgroup.subgroupOf, ← hmap,
      Subgroup.comap_map_eq_self_of_injective K0.subtype_injective]
  have h3 : (M.subgroupOf K0).map π = ⊥ := by
    rw [show M.subgroupOf K0 = π.ker from (QuotientGroup.ker_mk' N).symm]
    exact Subgroup.map_ker_self π
  have h4 : (C.subgroupOf K0).map π = Subgroup.closure ({a, b} : Set (↥K0 ⧸ N)) := by
    rw [hCsub, MonoidHom.map_closure, Set.image_pair]
  have h2 : (⊤ : Subgroup ↥K0) = M.subgroupOf K0 ⊔ C.subgroupOf K0 :=
    (Subgroup.subgroupOf_self (H := K0)).symm.trans
      (Subgroup.subgroupOf_sup hMleK0 (le_sup_right : C ≤ M ⊔ C))
  have htop : Subgroup.closure ({a, b} : Set (↥K0 ⧸ N)) = ⊤ := by
    have h1 : (⊤ : Subgroup ↥K0).map π = ⊤ :=
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)
    have hthis : (⊤ : Subgroup ↥K0).map π = Subgroup.closure ({a, b} : Set (↥K0 ⧸ N)) := by
      rw [h2, Subgroup.map_sup, h3, h4, bot_sup_eq]
    rw [← hthis]
    exact h1
  have hQr : IsPGroup r (↥K0 ⧸ N) :=
    (htop ▸ isPGroup_closure_pair_of_pow (p := r) hab ha_pow hb_pow).of_equiv Subgroup.topEquiv
  obtain ⟨P⟩ : Nonempty (Sylow r ↥K0) := inferInstance
  let Q₀ : Subgroup G := (P : Subgroup ↥K0).map K0.subtype
  have hQ₀syl : IsSylowIn r K0 Q₀ := by
    refine ⟨Subgroup.map_subtype_le _, P.2.map _, ?_⟩
    have hsub : Q₀.subgroupOf K0 = (P : Subgroup ↥K0) := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K0.subtype_injective]
    rw [Subgroup.relIndex, hsub]
    exact P.not_dvd_index
  have hdecomp : ∀ x ∈ K0, ∃ m ∈ M, ∃ q ∈ Q₀, x = m * q :=
    sylow_decomp_of_surjective π (QuotientGroup.mk'_surjective N)
      (QuotientGroup.ker_mk' N) hQr hQ₀syl
  have hCMQ₀ : ∀ m ∈ M, (∀ q ∈ Q₀, q * m * q⁻¹ = m) → m = 1 := by
    intro m hm hfix
    obtain ⟨m₀, hm₀, q₀, hq₀, hg₀eq⟩ := hdecomp g₀ hg₀K0
    have hfix₀ : q₀ * m * q₀⁻¹ = m := hfix q₀ hq₀
    have hg₀fix : g₀ * m * g₀⁻¹ = m := by
      rw [hg₀eq,
        show m₀ * q₀ * m * (m₀ * q₀)⁻¹ = m₀ * (q₀ * m * q₀⁻¹) * m₀⁻¹ by group, hfix₀,
        hMab m₀ hm₀ m hm]
      group
    exact hg₀f m hm hg₀fix
  have hQ₀M : ∀ x ∈ Q₀, x ∈ M → x = 1 := fun x hxQ hxM =>
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne r 2 hr2 Q₀ M hQ₀syl.2.1 hM2p) hxQ hxM
  have hconj2 : MulAut.conj t * MulAut.conj t = 1 := by rw [← map_mul, htt, map_one]
  have hconj_g₀ : (MulAut.conj t).toMonoidHom g₀ = g₁ := by simp [g₁, MulAut.conj_apply]
  have hconj_g₁ : (MulAut.conj t).toMonoidHom g₁ = g₀ := by
    change MulAut.conj t (MulAut.conj t g₀) = g₀
    rw [← MulAut.mul_apply, hconj2, MulAut.one_apply]
  have htM' : M.map (MulAut.conj t).toMonoidHom = M := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using htM y hy
    · intro x hx
      refine ⟨MulAut.conj t x, ?_, ?_⟩
      · rw [MulAut.conj_apply]; exact htM x hx
      · change MulAut.conj t (MulAut.conj t x) = x
        rw [← MulAut.mul_apply, hconj2, MulAut.one_apply]
  have htC' : C.map (MulAut.conj t).toMonoidHom = C := by
    change (Subgroup.closure ({g₀, g₁} : Set G)).map (MulAut.conj t).toMonoidHom =
      Subgroup.closure ({g₀, g₁} : Set G)
    rw [MonoidHom.map_closure, Set.image_pair]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx, hconj_g₀]; exact Subgroup.subset_closure (by right; rfl)
      · rw [hx, hconj_g₁]; exact Subgroup.subset_closure (by left; rfl)
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx, ← hconj_g₁]; exact Subgroup.subset_closure (by right; rfl)
      · rw [hx, ← hconj_g₀]; exact Subgroup.subset_closure (by left; rfl)
  have htK0 : t ∈ Subgroup.normalizer (K0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (M ⊔ C).map (MulAut.conj t).toMonoidHom = M ⊔ C
    rw [Subgroup.map_sup, htM', htC']
  obtain ⟨x, hxK0, hxeq⟩ :=
    exists_conjSub_eq_of_isSylowIn hQ₀syl (isSylowIn_conjSub hQ₀syl htK0)
  obtain ⟨m, hm, q, hq, hxmq⟩ := hdecomp x hxK0
  have hqQ₀ : conjSub q Q₀ = Q₀ := by
    rw [conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hq)
  have htQ₀_eq : conjSub t Q₀ = conjSub m Q₀ := by
    rw [← hxeq, hxmq, conjSub_mul, hqQ₀]
  let t' : G := m⁻¹ * t
  have ht'Q₀ : conjSub t' Q₀ = Q₀ := by
    change conjSub (m⁻¹ * t) Q₀ = Q₀
    rw [conjSub_mul, htQ₀_eq]
    rw [← conjSub_mul, inv_mul_cancel]
    have hconj1 : MulAut.conj (1 : G) = 1 := by ext x; simp [MulAut.conj_apply]
    change Q₀.map (MulAut.conj (1 : G)).toMonoidHom = Q₀
    rw [hconj1]
    exact Subgroup.map_id Q₀
  have ht'2pow : t' ^ 2 = m⁻¹ * (t * m⁻¹ * t⁻¹) := by
    change (m⁻¹ * t) ^ 2 = m⁻¹ * (t * m⁻¹ * t⁻¹)
    rw [pow_two, htinv]; group
  have ht'2M : t' ^ 2 ∈ M := by
    rw [ht'2pow]; exact mul_mem (inv_mem hm) (htM _ (inv_mem hm))
  have ht'2comm : ∀ q ∈ Q₀, q * t' ^ 2 * q⁻¹ = t' ^ 2 := by
    intro q hq₀
    have hqK0 : q ∈ K0 := hQ₀syl.1 hq₀
    have hcomM : ⁅t' ^ 2, q⁆ ∈ M := by
      have h1 : q * t' ^ 2 * q⁻¹ ∈ M := hMK q (hK0K hqK0) (t' ^ 2) ht'2M
      have h2 : t' ^ 2 * (q * t' ^ 2 * q⁻¹)⁻¹ ∈ M := mul_mem ht'2M (inv_mem h1)
      simpa [commutatorElement_def, mul_assoc] using h2
    have hcomQ : ⁅t' ^ 2, q⁆ ∈ Q₀ := by
      have ht'2N : t' ^ 2 ∈ Subgroup.normalizer (Q₀ : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change conjSub (t' ^ 2) Q₀ = Q₀
        rw [pow_two, conjSub_mul, ht'Q₀, ht'Q₀]
      have h1 : t' ^ 2 * q * (t' ^ 2)⁻¹ ∈ Q₀ :=
        (Subgroup.mem_normalizer_iff.mp ht'2N q).mp hq₀
      exact mul_mem h1 (inv_mem hq₀)
    have h1 : ⁅t' ^ 2, q⁆ = 1 := hQ₀M _ hcomQ hcomM
    have h2 : t' ^ 2 * q = q * t' ^ 2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [← h2]; group
  have ht'2 : t' ^ 2 = 1 := hCMQ₀ (t' ^ 2) ht'2M ht'2comm
  have hm1 : m⁻¹ = m := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hM2 m hm
  have hmt : t * m * t⁻¹ = m := by
    have h1 : m⁻¹ * (t * m⁻¹ * t⁻¹) = 1 := by rw [← ht'2pow]; exact ht'2
    have h2 : t * m⁻¹ * t⁻¹ = m := by
      have := congrArg (fun z => m * z) h1
      simpa [mul_assoc] using this
    simpa [hm1] using h2
  obtain ⟨u, hu, hmu⟩ := hI m hm hmt
  have ht'_eq : t' = u * t * u⁻¹ := by
    change m⁻¹ * t = u * t * u⁻¹
    have hmt' : t = m⁻¹ * (u * t * u⁻¹) := by rw [← hmu]; group
    conv_lhs => rw [hmt']
    rw [← mul_assoc, show m⁻¹ * m⁻¹ = 1 by rw [hm1, ← pow_two, hM2 m hm], one_mul]
  let Q : Subgroup G := conjSub u⁻¹ Q₀
  have huK0 : u ∈ K0 := hMleK0 hu
  have hQsyl : IsSylowIn r K0 Q :=
    isSylowIn_conjSub hQ₀syl (Subgroup.le_normalizer (inv_mem huK0))
  have hQdecomp : ∀ x ∈ K0, ∃ m ∈ M, ∃ q ∈ Q, x = m * q :=
    sylow_decomp_of_surjective π (QuotientGroup.mk'_surjective N)
      (QuotientGroup.ker_mk' N) hQr hQsyl
  have hQM : ∀ x ∈ Q, x ∈ M → x = 1 := fun x hxQ hxM =>
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne r 2 hr2 Q M hQsyl.2.1 hM2p) hxQ hxM
  have hQt : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    have htQ : t ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change conjSub t (conjSub u⁻¹ Q₀) = conjSub u⁻¹ Q₀
      rw [← conjSub_mul, show t * u⁻¹ = u⁻¹ * (u * t * u⁻¹) by group, conjSub_mul,
        show conjSub (u * t * u⁻¹) Q₀ = Q₀ by rw [← ht'_eq]; exact ht'Q₀]
    intro q hq
    exact (Subgroup.mem_normalizer_iff.mp htQ q).mp hq
  have hCMQ : ∀ m ∈ M, (∀ q ∈ Q, q * m * q⁻¹ = m) → m = 1 := by
    intro m hm hfix
    apply hCMQ₀ m hm
    intro q₀ hq₀
    have hq : u⁻¹ * q₀ * u ∈ Q :=
      Subgroup.mem_map.mpr ⟨q₀, hq₀, by simp [conjSub, MulAut.conj_apply]⟩
    have h1 : (u⁻¹ * q₀ * u) * m * (u⁻¹ * q₀ * u)⁻¹ = m := hfix _ hq
    have hum : u * m * u⁻¹ = m := by rw [hMab u hu m hm]; group
    have h1u : u * ((u⁻¹ * q₀ * u) * m * (u⁻¹ * q₀ * u)⁻¹) * u⁻¹ = u * m * u⁻¹ := by
      rw [h1]
    have hsimp : u * ((u⁻¹ * q₀ * u) * m * (u⁻¹ * q₀ * u)⁻¹) * u⁻¹ =
        q₀ * (u * m * u⁻¹) * q₀⁻¹ := by group
    rw [hsimp, hum] at h1u
    exact h1u
  exact ⟨K0, Q, hMleK0, hK0K, hK0norm, hcentK0, hQdecomp, hQsyl, hQt, hCMQ, hQM⟩

end CFSG.OddStandard.HigherRank.YamadaG23
