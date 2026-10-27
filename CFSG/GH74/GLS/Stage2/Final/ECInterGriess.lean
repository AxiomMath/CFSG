module

public import CFSG.GH74.GLS.Stage2.Final.LayerLift
public import CFSG.GH74.GLS.Stage2.Final.ClassicalLocal
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.Generic.GKFTables
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.GLS.Stage2.Final.ECInterGriess

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.LayerLift
open scoped commutatorElement

section
variable {X : Type*} [Group X]

theorem exists_lift_component (N : Subgroup X) [N.Normal] [IsCyclic ↥N] (Kb : Subgroup (X ⧸ N))
    (hKb : IsComponent Kb) :
    ∃ K : Subgroup X, IsQuasisimple ↥K ∧ K.IsSubnormal ∧ K.map (QuotientGroup.mk' N) = Kb ∧
      K ≤ Kb.comap (QuotientGroup.mk' N) ∧
      (∀ J : Subgroup X, J ≤ Kb.comap (QuotientGroup.mk' N) → Group.IsPerfect ↥J → J ≤ K) := by
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  set Kt : Subgroup X := Kb.comap π with hKt
  have hsub : Kt.IsSubnormal := hKb.2.comap π
  have hmap : Kt.map π = Kb := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kb
  have hNKt : N ≤ Kt := by
    intro n hn
    show π n ∈ Kb
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hperfKb : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.mp hKb.1.1
  have hperfKt : ⁅Kt.map π, Kt.map π⁆ = Kt.map π := by rw [hmap]; exact hperfKb
  have hcent : ∀ k ∈ Kt, ∀ n ∈ N, k * n = n * k := fun k hk n hn =>
    centralizes_of_perfect_quotient N Kt hperfKt hk hn
  let f : ↥Kt →* ↥Kb := π.subgroupComap Kb
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (b : X ⧸ N)
    have hxKt : x ∈ Kt := by
      show π x ∈ Kb
      rw [hπ, hx]
      exact b.2
    exact ⟨⟨x, hxKt⟩, Subtype.ext hx⟩
  have hker : f.ker ≤ center ↥Kt := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxN : (x : X) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact Subtype.ext (hcent y.1 y.2 x hxN)
  have hq : IsQuasisimple ↥(commutator ↥Kt) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hker hKb.1
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective f hf hker hKb.1.1
  set K : Subgroup X := (commutator ↥Kt).map Kt.subtype with hK
  have hKle : K ≤ Kt := Subgroup.map_subtype_le _
  have hqK : IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator ↥Kt).equivMapOfInjective Kt.subtype Kt.subtype_injective) hq
  have hKsn : K.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hKle ?_ hsub
    have h : K.subgroupOf Kt = commutator ↥Kt := by
      show Subgroup.comap Kt.subtype K = _
      rw [hK, Subgroup.comap_map_eq_self_of_injective Kt.subtype_injective]
    rw [h]
    exact Subgroup.Normal.isSubnormal inferInstance
  have hKeq : K = ⁅Kt, Kt⁆ := by
    have h0 : commutator ↥Kt = ⁅(⊤ : Subgroup ↥Kt), ⊤⁆ := rfl
    rw [hK, h0, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨K, hqK, hKsn, ?_, hKle, ?_⟩
  · apply le_antisymm
    · rw [← hmap]; exact Subgroup.map_mono hKle
    · intro b hb
      obtain ⟨c, hc⟩ := hsurj ⟨b, hb⟩
      have hcK : ((c : ↥Kt) : X) ∈ K := ⟨(c : ↥Kt), c.2, rfl⟩
      exact ⟨((c : ↥Kt) : X), hcK, congrArg Subtype.val hc⟩
  · intro J hJ hJp
    have h1 : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJp
    rw [hKeq, ← h1]
    exact Subgroup.commutator_mono hJ hJ

end

section Hopf

open CFSG.ComponentClassification.TBLit CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.RankThree.PerfectCover
  CFSG.GH74.Generic CFSG.Assembly.LowTwoRank

theorem card_hopf_psl2 (hGA : GriessMultipliersAllModels) {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (hq3 : 3 < p ^ f) :
    Nat.card (hopfMultiplier (StatedProj (StatedSL 2 F))) =
      2 * ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
  have hoddp : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hadm : StatedLieAdmissible .PSL 2 p f :=
    ⟨hp, hf, le_refl 2, fun h => by have := (Prod.mk.inj h).2; omega,
      fun h => by have := (Prod.mk.inj h).2; omega⟩
  have hmJ : CFSG.Models.LieModel (StatedProj (StatedSL 2 F)) .PSL 2 p f :=
    ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩⟩
  have hgen : (genericOrders .PSL 2 p f) = (2, 1) := by
    have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
      obtain ⟨k, hk⟩ := hoddp
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    exact Prod.ext h1 rfl
  rw [card_hopfMultiplier_of_griess hGA hmJ, hgen]
  simp

theorem exceptionalOrders_psl2 {p f : ℕ} (hp2 : p ≠ 2) :
    exceptionalOrders .PSL 2 p f = (1, 1) ∨ (p = 3 ∧ f = 2 ∧ exceptionalOrders .PSL 2 p f = (3, 1)) := by
  unfold exceptionalOrders
  split <;> simp_all

end Hopf

section Core

open CFSG.ComponentClassification.TBLit CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.RankThree.PerfectCover
  CFSG.GH74.Generic CFSG.Assembly.LowTwoRank

theorem exists_prime_pow_card' (F : Type) [Field F] [Finite F] :
    ∃ (p n : ℕ), p.Prime ∧ 1 ≤ n ∧ Nat.card F = p ^ n := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp0⟩ : ∃ p, CharP F p := ⟨ringChar F, ringChar.charP F⟩
  obtain ⟨n, hp, hpn⟩ := FiniteField.card F p
  exact ⟨p, n, hp, n.pos, by rw [Nat.card_eq_fintype_card]; exact hpn⟩

theorem statedScalars_central {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem lift_inf_eq_bot (hGA : GriessMultipliersAllModels) {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] [IsCyclic ↥N] (hNodd : Odd (Nat.card ↥N))
    (L : Subgroup (X ⧸ N)) (K : Subgroup X) (hK : IsQuasisimple ↥K)
    (hKL : K.map (QuotientGroup.mk' N) = L)
    (hcent : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k)
    (q : ℕ) (hq : Odd q) (hq3 : 3 < q) (hL : HasSL2Model ↥L (fun r => r = q))
    (h9 : q = 9 → ¬ 3 ∣ Nat.card ↥N) :
    K ⊓ N = ⊥ := by
  classical
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := hL
  have hFq' : Nat.card F = q := hFq
  obtain ⟨p, n, hp, hn, hcard⟩ := exists_prime_pow_card' F
  have hoddq : Odd (p ^ n) := by rw [← hcard, hFq']; exact hq
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact (Nat.not_even_iff_odd.2 hoddq) this
  have hq3' : 3 < p ^ n := by rw [← hcard, hFq']; exact hq3
  have hhopf := card_hopf_psl2 hGA hp hp2 hn hcard hq3'
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have : Group.IsPerfect ↥K := hK.1
  let f₀ : ↥K →* ↥L := (π.comp K.subtype).codRestrict L (fun k => by rw [← hKL]; exact ⟨k, k.2, rfl⟩)
  have hf₀_apply : ∀ k : ↥K, ((f₀ k : ↥L) : X ⧸ N) = π (k : X) := fun k => rfl
  have hf₀ : Function.Surjective f₀ := by
    intro l
    have hl : (l : X ⧸ N) ∈ K.map π := by rw [hKL]; exact l.2
    obtain ⟨k, hk, hkl⟩ := hl
    exact ⟨⟨k, hk⟩, Subtype.ext (by rw [hf₀_apply]; exact hkl)⟩
  let ψ : ↥K →* StatedProj (StatedSL 2 F) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))).comp
      (e.toMonoidHom.comp f₀)
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp hf₀)
  have hker : ψ.ker ≤ center ↥K := by
    intro w hw
    have hw' : e (f₀ w) ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hw)
    have hwc : e (f₀ w) ∈ Subgroup.center ↥(StatedSL 2 F) := statedScalars_central _ hw'
    have hcl : ∀ l : ↥L, (f₀ w) * l = l * (f₀ w) := fun l => e.injective (by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp hwc (e l)).symm)
    have hcomm : ∀ y : ↥K, ⁅w, y⁆ ∈ center ↥K := by
      intro y
      have h1 : f₀ ⁅w, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcl (f₀ y))
      have h2 : π ((⁅w, y⁆ : ↥K) : X) = 1 := by
        have := congrArg Subtype.val h1
        rwa [hf₀_apply] at this
      have hN1 : ((⁅w, y⁆ : ↥K) : X) ∈ N := (QuotientGroup.eq_one_iff _).mp h2
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hcent k.1 k.2 _ hN1)
    let g : ↥K →* ↥(center ↥K) :=
      { toFun := fun y => ⟨⁅w, y⁆, hcomm y⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y₁ y₂ => by
          apply Subtype.ext
          have hc : (y₁ : ↥K) * ⁅w, y₂⁆ * y₁⁻¹ = ⁅w, y₂⁆ := by
            have := Subgroup.mem_center_iff.mp (hcomm y₂) y₁
            calc y₁ * ⁅w, y₂⁆ * y₁⁻¹ = (⁅w, y₂⁆ * y₁) * y₁⁻¹ := by rw [this]
              _ = ⁅w, y₂⁆ := by group
          calc (⁅w, y₁ * y₂⁆ : ↥K) = ⁅w, y₁⁆ * (y₁ * ⁅w, y₂⁆ * y₁⁻¹) := by
                simp only [commutatorElement_def]; group
            _ = ⁅w, y₁⁆ * ⁅w, y₂⁆ := by rw [hc] }
    have hg : ∀ y : ↥K, g y = 1 := by
      have h0 : commutator ↥K ≤ g.ker := Abelianization.commutator_subset_ker g
      have h1 : g.ker = ⊤ := by
        rw [eq_top_iff]
        have := Group.IsPerfect.commutator_eq_top (G := ↥K)
        rw [← this]
        exact h0
      intro y
      have hy : y ∈ g.ker := by rw [h1]; trivial
      exact MonoidHom.mem_ker.mp hy
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : ⁅w, y⁆ = 1 := congrArg Subtype.val (hg y)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hdvd1 := card_ker_dvd_hopfMultiplier hK.1 ψ hψs hker
  rw [hhopf] at hdvd1
  have hDle : (K ⊓ N).subgroupOf K ≤ ψ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    rw [MonoidHom.mem_ker]
    have h1 : f₀ x = 1 := Subtype.ext (by rw [hf₀_apply]; exact (QuotientGroup.eq_one_iff _).mpr hx.2)
    simp [ψ, h1]
  have hD1 : Nat.card ↥((K ⊓ N).subgroupOf K) ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_le hDle
  have hDcard : Nat.card ↥((K ⊓ N).subgroupOf K) = Nat.card ↥(K ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ N ≤ K)).toEquiv
  have hD2 : Nat.card ↥(K ⊓ N) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_right
  have hDodd : Odd (Nat.card ↥(K ⊓ N)) := Odd.of_dvd_nat hNodd hD2
  have hcop : Nat.Coprime (Nat.card ↥(K ⊓ N)) 2 := hDodd.coprime_two_right
  have hdvd2 : Nat.card ↥(K ⊓ N) ∣
      (exceptionalOrders .PSL 2 p n).1 * (exceptionalOrders .PSL 2 p n).2 := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [← hDcard]
    exact hD1.trans hdvd1
  have hD1' : Nat.card ↥(K ⊓ N) = 1 := by
    rcases exceptionalOrders_psl2 (f := n) hp2 with h | ⟨hp3, hn2, h⟩
    · rw [h] at hdvd2
      simpa using hdvd2
    · rw [h] at hdvd2
      have hq9 : q = 9 := by rw [← hFq', hcard, hp3, hn2]; norm_num
      have h3 := h9 hq9
      have hdvd3 : Nat.card ↥(K ⊓ N) ∣ 3 := by simpa using hdvd2
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3'
      · exact h1
      · exact absurd (h3' ▸ hD2) h3
  exact (Subgroup.eq_bot_iff_card _).mpr hD1'


theorem commute_of_comm_mem {X : Type*} [Group X] (K : Subgroup X) [Group.IsPerfect ↥K] (Z : Subgroup X)
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (a : X) (ha : ∀ b ∈ K, ⁅a, b⁆ ∈ Z) : ∀ b ∈ K, a * b = b * a := by
  let _ : CommGroup ↥Z := { (inferInstance : Group ↥Z) with mul_comm := fun x y => Subtype.ext (hZ x.1 x.2 y.1 y.2) }
  let g : ↥K →* ↥Z :=
    { toFun := fun b => ⟨⁅a, (b : X)⁆, ha b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b₁ b₂ => by
        apply Subtype.ext
        have hc : (b₁ : X) * ⁅a, (b₂ : X)⁆ * (b₁ : X)⁻¹ = ⁅a, (b₂ : X)⁆ := by
          have := hKZ b₁ b₁.2 _ (ha b₂ b₂.2)
          calc (b₁ : X) * ⁅a, (b₂ : X)⁆ * (b₁ : X)⁻¹ = (⁅a, (b₂ : X)⁆ * b₁) * (b₁ : X)⁻¹ := by rw [this]
            _ = ⁅a, (b₂ : X)⁆ := by group
        calc (⁅a, ((b₁ * b₂ : ↥K) : X)⁆ : X) = ⁅a, (b₁ : X)⁆ * ((b₁ : X) * ⁅a, (b₂ : X)⁆ * (b₁ : X)⁻¹) := by
              simp only [Subgroup.coe_mul, commutatorElement_def]; group
          _ = ⁅a, (b₁ : X)⁆ * ⁅a, (b₂ : X)⁆ := by rw [hc] }
  have h0 : commutator ↥K ≤ g.ker := Abelianization.commutator_subset_ker g
  have h1 : g.ker = ⊤ := by
    rw [eq_top_iff]
    have := Group.IsPerfect.commutator_eq_top (G := ↥K)
    rw [← this]
    exact h0
  intro b hb
  have hy : (⟨b, hb⟩ : ↥K) ∈ g.ker := by rw [h1]; trivial
  have h2 : g ⟨b, hb⟩ = 1 := MonoidHom.mem_ker.mp hy
  have h3 : ⁅a, b⁆ = 1 := congrArg Subtype.val h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem eq_one_of_sq_eq_one_of_odd {X : Type*} [Group X] (N : Subgroup X) (hN : Odd (Nat.card ↥N)) {x : X}
    (hx : x ∈ N) (hx2 : x * x = 1) : x = 1 := by
  let y : ↥N := ⟨x, hx⟩
  have hy2 : y ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hx2)
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have h2 : orderOf y ∣ Nat.card ↥N := orderOf_dvd_natCard y
  have h3 : orderOf y ∣ Nat.gcd 2 (Nat.card ↥N) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card ↥N) = 1 := (Nat.coprime_comm.mp hN.coprime_two_right)
  rw [h4] at h3
  have h5 : y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  exact congrArg Subtype.val h5

theorem layer_inf_eq_bot (hGA : GriessMultipliersAllModels) {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] [IsCyclic ↥N] (hNodd : Odd (Nat.card ↥N))
    (L₁ L₂ : Subgroup (X ⧸ N)) (q : ℕ) (hq : Odd q) (hq3 : 3 < q)
    (hcomps : {K : Subgroup (X ⧸ N) | IsComponent K} = {L₁, L₂})
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hinf : Nat.card ↥(L₁ ⊓ L₂) = 2)
    (hsl₁ : HasSL2Model ↥L₁ (fun r => r = q)) (hsl₂ : HasSL2Model ↥L₂ (fun r => r = q))
    (h9 : q = 9 → ¬ 3 ∣ Nat.card ↥N) :
    layer X ⊓ N = ⊥ := by
  classical
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hL₁c : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup (X ⧸ N) | IsComponent K} := by rw [hcomps]; simp
    exact this
  have hL₂c : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup (X ⧸ N) | IsComponent K} := by rw [hcomps]; simp
    exact this
  obtain ⟨K₁, hq₁, hs₁, hm₁, hle₁, hper₁⟩ := exists_lift_component N L₁ hL₁c
  obtain ⟨K₂, hq₂, hs₂, hm₂, hle₂, hper₂⟩ := exists_lift_component N L₂ hL₂c
  have hcent₁ : ∀ k ∈ K₁, ∀ n ∈ N, k * n = n * k := fun k hk n hn =>
    centralizes_of_perfect_quotient N K₁ (by rw [hm₁]; exact Subgroup.isPerfect_iff.mp hL₁c.1.1) hk hn
  have hcent₂ : ∀ k ∈ K₂, ∀ n ∈ N, k * n = n * k := fun k hk n hn =>
    centralizes_of_perfect_quotient N K₂ (by rw [hm₂]; exact Subgroup.isPerfect_iff.mp hL₂c.1.1) hk hn
  have hK₁ : K₁ ⊓ N = ⊥ := lift_inf_eq_bot hGA N hNodd L₁ K₁ hq₁ hm₁ hcent₁ q hq hq3 hsl₁ h9
  have hK₂ : K₂ ⊓ N = ⊥ := lift_inf_eq_bot hGA N hNodd L₂ K₂ hq₂ hm₂ hcent₂ q hq hq3 hsl₂ h9
  have hlayer : layer X ≤ K₁ ⊔ K₂ := by
    refine sSup_le fun J hJ => ?_
    have hnot : ¬ J ≤ π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      intro hle
      have hsolvN : Group.IsSolvable ↥N := inferInstance
      have hsolvJ : Group.IsSolvable ↥J :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
      have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
      have := hJ.1.1
      exact Group.IsPerfect.not_isSolvable ↥J hsolvJ
    have hJc : IsComponent (J.map π) :=
      ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩
    have hmem : J.map π ∈ ({L₁, L₂} : Set (Subgroup (X ⧸ N))) := by rw [← hcomps]; exact hJc
    have hperJ : Group.IsPerfect ↥J := hJ.1.1
    rcases hmem with h | h
    · exact le_sup_of_le_left (hper₁ J (by rw [← Subgroup.map_le_iff_le_comap]; exact h.le) hperJ)
    · exact le_sup_of_le_right (hper₂ J (by rw [← Subgroup.map_le_iff_le_comap]; exact h.le) hperJ)
  have hK12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
    intro a ha
    have : Group.IsPerfect ↥K₂ := hq₂.1
    let _ : CommGroup ↥N := IsCyclic.commGroup
    refine commute_of_comm_mem K₂ N (fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥N) ⟨y, hy⟩)) hcent₂ a ?_
    intro b hb
    have h1 : π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      have hπa : π a ∈ L₁ := by rw [← hm₁]; exact ⟨a, ha, rfl⟩
      have hπb : π b ∈ L₂ := by rw [← hm₂]; exact ⟨b, hb, rfl⟩
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ hπa _ hπb)
    exact (QuotientGroup.eq_one_iff _).mp h1
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b}
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have h := hK12 a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have h := hK12 a ha b hb
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := by
            have := hK12 a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
            exact this.symm }
  have hPle : K₁ ⊔ K₂ ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩) (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxN⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hPle (hlayer hxE)
  have hπa : π a ∈ L₁ := by rw [← hm₁]; exact ⟨a, ha, rfl⟩
  have hπb : π b ∈ L₂ := by rw [← hm₂]; exact ⟨b, hb, rfl⟩
  have hπx : π a * π b = 1 := by
    rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).mpr hxN
  have hπa2 : π a ∈ L₂ := by
    have : π a = (π b)⁻¹ := eq_inv_of_mul_eq_one_left hπx
    rw [this]; exact L₂.inv_mem hπb
  have hsq : ∀ g : X ⧸ N, g ∈ L₁ ⊓ L₂ → g * g = 1 := by
    intro g hg
    have h1 : (⟨g, hg⟩ : ↥(L₁ ⊓ L₂)) ^ Nat.card ↥(L₁ ⊓ L₂) = 1 := pow_card_eq_one'
    rw [hinf] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have ha2 : a * a = 1 := by
    have h1 : π (a * a) = 1 := by rw [map_mul]; exact hsq _ ⟨hπa, hπa2⟩
    have h2 : a * a ∈ K₁ ⊓ N := ⟨mul_mem ha ha, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [hK₁] at h2
    exact h2
  have hb2 : b * b = 1 := by
    have hπb' : π b ∈ L₁ ⊓ L₂ := by
      have : π b = (π a)⁻¹ := eq_inv_of_mul_eq_one_right hπx
      refine ⟨?_, hπb⟩
      rw [this]; exact L₁.inv_mem hπa
    have h1 : π (b * b) = 1 := by rw [map_mul]; exact hsq _ hπb'
    have h2 : b * b ∈ K₂ ⊓ N := ⟨mul_mem hb hb, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [hK₂] at h2
    exact h2
  have hx2 : (a * b) * (a * b) = 1 := by
    have h := hK12 a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← h]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2]; simp
  exact eq_one_of_sq_eq_one_of_odd N hNodd hxN hx2

end Core

section Top

open CFSG.ComponentClassification.TBLit CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Final

theorem ecInter_of_griess (hGA : GriessMultipliersAllModels) (h2 : Stage2Main) : ECInter := by
  intro G _ _ z k S hctx hk
  rcases hk with rfl | ⟨ε, rfl⟩
  · have h0 := (h2 G z Kind.psp4 S hctx).oddCore (fun ε h => by cases h)
    have : OddCore z = ⊥ := by
      unfold OddCore pPrimeCoreOf
      rw [h0, Subgroup.map_bot]
    rw [this, inf_bot_eq]
  · obtain ⟨q, L₁, L₂, hL⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1L4 G z S ε q L₁ L₂ := by
      cases hctx.data with
      | l4 _ h => exact h
    obtain ⟨hcyc, hdvd⟩ := (h2 G z (Kind.l4 ε) S hctx).oddCoreL4 ε q L₁ L₂ rfl hL
    have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
    have : IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) := hcyc
    have h9 : q = 9 → ¬ 3 ∣ Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := by
      intro hq9 h3
      have h4 := h3.trans hdvd
      subst hq9
      split_ifs at h4 <;> omega
    have hX := layer_inf_eq_bot hGA (pPrimeCore 2 ↥(Cen z)) hNodd L₁ L₂ q hL.pair.odd hL.pair.gt3
      hL.pair.comps hL.pair.prod.2.1 hL.pair.prod.2.2 hL.pair.sl₁ hL.pair.sl₂ h9
    have hmap2 : (layer ↥(Cen z)).map (Cen z).subtype ⊓ (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥ := by
      rw [← Subgroup.map_inf _ _ _ (Cen z).subtype_injective, hX, Subgroup.map_bot]
    exact hmap2

end Top

end CFSG.GH74.GLS.Stage2.Final.ECInterGriess
