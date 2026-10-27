module

public import CFSG.GH74.Generic.S1.Exo.Glue
public import CFSG.GH74.Generic.S1.Exo.Leaf

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem exists_odd_prime_dvd_sq_add_one {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ q ^ 2 + 1 := by
  have hq' : q % 2 = 1 := Nat.odd_iff.1 hq
  have h4 : (q ^ 2 + 1) % 4 = 2 := by
    have : q ^ 2 % 8 = 1 := by
      have key : ∀ r : Fin 8, r.val % 2 = 1 → r.val ^ 2 % 8 = 1 := by decide
      have := key ⟨q % 8, Nat.mod_lt _ (by norm_num)⟩ (by simp only; omega)
      rw [Nat.pow_mod]
      exact this
    omega
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 + 1 = 2 * m := ⟨(q ^ 2 + 1) / 2, by omega⟩
  have hmodd : m % 2 = 1 := by omega
  have hm1 : m ≠ 1 := by
    intro h
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_⟩
  · intro h
    have h2 : 2 ∣ m := h ▸ Nat.minFac_dvd m
    omega
  · rw [hm]
    exact Dvd.dvd.mul_left (Nat.minFac_dvd m) 2

theorem perfect_le_of_hall {Γ : Type*} [Group Γ] {z : Γ} (hz : z ∈ Subgroup.center Γ)
    {Ω Fx P : Subgroup Γ} (hP : ⁅P, P⁆ = P) (hPF : P ≤ Fx)
    (hall : ∀ k ∈ Fx, k ∈ Ω ∨ z * k ∈ Ω) : P ≤ Ω := by
  have hcomm : ∀ a b : Γ, a ∈ Fx → b ∈ Fx → ⁅a, b⁆ ∈ Ω := by
    intro a b ha hb
    have hza : ∀ c : Γ, ⁅z * c, b⁆ = ⁅c, b⁆ := by
      intro c
      have h1 := Subgroup.mem_center_iff.1 hz
      simp only [commutatorElement_def, mul_inv_rev]
      calc z * c * b * (c⁻¹ * z⁻¹) * b⁻¹ = z * (c * b * c⁻¹) * z⁻¹ * b⁻¹ := by group
        _ = (c * b * c⁻¹) * z * z⁻¹ * b⁻¹ := by rw [← h1 (c * b * c⁻¹)]
        _ = c * b * c⁻¹ * b⁻¹ := by group
    have hzb : ∀ c : Γ, ⁅c, z * b⁆ = ⁅c, b⁆ := by
      intro c
      have h1 := Subgroup.mem_center_iff.1 hz
      simp only [commutatorElement_def, mul_inv_rev]
      calc c * (z * b) * c⁻¹ * (b⁻¹ * z⁻¹) = c * z * b * c⁻¹ * b⁻¹ * z⁻¹ := by group
        _ = z * c * b * c⁻¹ * b⁻¹ * z⁻¹ := by rw [← h1 c]
        _ = z * (c * b * c⁻¹ * b⁻¹) * z⁻¹ := by group
        _ = c * b * c⁻¹ * b⁻¹ := by rw [← h1 (c * b * c⁻¹ * b⁻¹)]; group
    rcases hall a ha with h1 | h1 <;> rcases hall b hb with h2 | h2
    · exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h1 h2) (Ω.inv_mem h1)) (Ω.inv_mem h2)
    · rw [← hzb]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h1 h2) (Ω.inv_mem h1)) (Ω.inv_mem h2)
    · rw [← hza]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h1 h2) (Ω.inv_mem h1)) (Ω.inv_mem h2)
    · rw [← hza, ← hzb]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h1 h2) (Ω.inv_mem h1)) (Ω.inv_mem h2)
  rw [← hP, Subgroup.commutator_def]
  refine (Subgroup.closure_le Ω).2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact hcomm a b (hPF ha) (hPF hb)


variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

theorem ExoticFixedGroup.exists_involution_card {Γ : Type} [Group Γ] {β : MulAut Γ} {z : Γ} {q : ℕ}
    (h : ExoticFixedGroup β z q) (hq : Odd q) (hq1 : 1 < q) :
    ∃ Ω : Subgroup Γ, (∀ k ∈ Ω, β k = k) ∧ IsSimpleGroup ↥Ω ∧ Group.IsPerfect ↥Ω ∧
      Nat.card ↥Ω * 2 = q ^ 2 * (q ^ 4 - 1) ∧ z ∉ Ω ∧ (∀ k : Γ, β k = k → k ∈ Ω ∨ z * k ∈ Ω) ∧
      ∃ u ∈ Ω, u * u = 1 ∧ u ≠ 1 := by
  obtain ⟨Ω, hfix, hs, hp, hc, -, -, hzΩ, hall⟩ := h
  refine ⟨Ω, hfix, hs, hp, hc, hzΩ, hall, ?_⟩
  have hne : Nat.card ↥Ω ≠ 0 := natCard_pos_aux hq1 hc
  have : Finite ↥Ω := Nat.finite_of_card_ne_zero hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥Ω := by
    have h4 : 4 ∣ Nat.card ↥Ω * 2 := by
      rw [hc]
      exact Dvd.dvd.mul_left (Dvd.dvd.trans (by norm_num : 4 ∣ 16) (sixteen_dvd_pow_four_sub_one hq)) _
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ω) 2 h2
  refine ⟨(x : Γ), x.2, ?_, ?_⟩
  · have : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
    exact congrArg Subtype.val this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem exotic_cmp (hExact : S1LiftExactProp)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) {q : ℕ} (hq1 : 1 < q)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hExo : IsExoticAutAt q α) {wK : ↥K} {w : G} (hwx : w ∈ centralizer ({x} : Set G))
    (hwK2 : wK * wK = 1) (hwKα : α wK = wK) (hwbar : barOf hwx = (wK : CentralizerBar x))
    {t : G} (ht : t = w * v) (hxt : x ∈ centralizer ({t} : Set G)) :
    ∃ P : Subgroup (CentralizerBar t), IsSimpleGroup ↥P ∧ Nat.card ↥P * 2 = q ^ 2 * (q ^ 4 - 1) ∧
      P ≤ layer (CentralizerBar t) ∧
      P ≤ centralizer ({proj t ⟨x, hxt⟩} : Set (CentralizerBar t)) ∧
      ∀ M : Subgroup (CentralizerBar t), ⁅M, M⁆ = M →
        M ≤ centralizer ({proj t ⟨x, hxt⟩} : Set (CentralizerBar t)) → M ≤ P := by
  classical
  have hqodd := hExo.odd
  have hx : orderOf x = 2 := hset.inv
  have hxK : xbar x ∈ K := hset.shape.2
  set z : ↥K := ⟨xbar x, hxK⟩ with hzdef
  have hzc : z ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  have hz1 : z ≠ 1 := fun h => xbar_ne_one hx (congrArg Subtype.val h)
  set D := layerOf hExact hset hfront e with hD
  have hE2 := (hExo.conj_mul hwK2 hwKα).exoticFixedGroup hzc hz1
  obtain ⟨Ω'', hfix'', hs'', hp'', hcard'', hz'', hall'', u, hu, hu2, hu1⟩ :=
    hE2.exists_involution_card hqodd hq1
  have htx : t ∈ centralizer ({x} : Set G) := by rw [ht]; exact Subgroup.mul_mem _ hwx hv
  have hbart : barOf htx = barOf hwx * barOf hv := by
    subst ht
    rfl
  have hα'coe : ∀ k : ↥K, (((MulAut.conj wK * α) k : ↥K) : CentralizerBar x) =
      barOf htx * (k : CentralizerBar x) * (barOf htx)⁻¹ := by
    intro k
    rw [MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα k, hbart, hwbar]
    group
  set ℓ : ↥K →* G := D.ι.comp e.toMonoidHom with hℓ
  have hℓinj : Function.Injective ℓ := D.ι_injective.comp e.injective
  have hℓx : ∀ k : ↥K, ℓ k ∈ centralizer ({x} : Set G) := fun k => D.ι_mem_cent (e k)
  have hℓt : ∀ k : ↥K, (MulAut.conj wK * α) k = k → ℓ k * t = t * ℓ k := by
    intro k hk
    show D.ι (e k) * t = t * D.ι (e k)
    refine D.ι_comm_of_fixed htx (s := e k) ?_
    have h1 : (D.iso.symm (e k) : ↥D.K) = k := e.symm_apply_apply k
    rw [h1, ← hα'coe k, hk]
  have hℓt' : ∀ k : ↥K, ℓ k * t = t * ℓ k → (MulAut.conj wK * α) k = k := by
    intro k hk
    have h2 := D.fixed_of_ι_comm htx (s := e k) hk
    have h1 : (D.iso.symm (e k) : ↥D.K) = k := e.symm_apply_apply k
    rw [h1] at h2
    apply Subtype.ext
    rw [hα'coe k]
    exact h2
  set Ωh : Subgroup G := Ω''.map ℓ with hΩh
  set V : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) with hV
  have hΩV : Ωh ≤ V := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨hℓx k, mem_centralizer_singleton_iff.2 (hℓt k (hfix'' k hk))⟩
  have hΩperf : ⁅Ωh, Ωh⁆ = Ωh := by
    rw [hΩh, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hp'']
  have hΩnontriv : Nontrivial ↥Ω'' := ⟨⟨⟨u, hu⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
  have hnonab : ∃ a b : ↥Ω'', a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative ↥Ω'' ⟨⟨fun a b => hcon a b⟩⟩
  have : IsSimpleGroup ↥Ω'' := hs''
  have hΩquasi0 := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  have hΩeq : ↥Ω'' ≃* ↥Ωh := Ω''.equivMapOfInjective ℓ hℓinj
  have hΩquasi : IsQuasisimple ↥Ωh := CFSG.LocalCores.isQuasisimple_of_mulEquiv hΩeq hΩquasi0
  have : IsSimpleGroup ↥Ωh := hΩeq.symm.isSimpleGroup
  have hperfV : ∀ A : Subgroup G, A ≤ V → ⁅A, A⁆ = A → A ≤ Ωh := by
    intro A hAV hAperf
    have hAx : A ≤ centralizer ({x} : Set G) := fun a ha => (hAV ha).1
    have hrange := D.le_range_ι hAperf hAx
    set P : Subgroup ↥K := A.comap ℓ with hP
    have hAr : A ≤ ℓ.range := by
      intro a ha
      obtain ⟨s, hs⟩ := hrange ha
      exact ⟨e.symm s, by simp [hℓ, hs]⟩
    have hmapP : P.map ℓ = A := by
      rw [hP, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hAr
    have hPperf : ⁅P, P⁆ = P := by
      apply Subgroup.map_injective hℓinj
      rw [Subgroup.map_commutator, hmapP, hAperf]
    have hPfix : P ≤ fixedSub (MulAut.conj wK * α) := by
      intro k hk
      have hkA : ℓ k ∈ A := hk
      exact hℓt' k (mem_centralizer_singleton_iff.1 (hAV hkA).2)
    have hPle : P ≤ Ω'' := perfect_le_of_hall hzc hPperf hPfix
      (fun k hk => hall'' k hk)
    intro a ha
    have : a ∈ P.map ℓ := by rw [hmapP]; exact ha
    obtain ⟨k, hk, hkeq⟩ := this
    exact ⟨k, hPle hk, hkeq⟩
  have hnorm : ∀ g ∈ V, ∀ u' ∈ Ωh, g * u' * g⁻¹ ∈ Ωh := by
    intro g hg u' hu'
    set A : Subgroup G := Ωh.map (MulAut.conj g).toMonoidHom with hA
    have hAperf : ⁅A, A⁆ = A := by rw [hA, ← Subgroup.map_commutator, hΩperf]
    have hAV : A ≤ V := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hΩV ha
      refine ⟨?_, ?_⟩
      · have hac : Commute a x := mem_centralizer_singleton_iff.1 h1.1
        have hgc : Commute g x := mem_centralizer_singleton_iff.1 hg.1
        have := (Commute.mul_left hgc hac).mul_left hgc.inv_left
        show (MulAut.conj g).toMonoidHom a ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff]
        simpa [MulAut.conj_apply] using this.eq
      · have hat : Commute a t := mem_centralizer_singleton_iff.1 h1.2
        have hgt : Commute g t := mem_centralizer_singleton_iff.1 hg.2
        have := (Commute.mul_left hgt hat).mul_left hgt.inv_left
        show (MulAut.conj g).toMonoidHom a ∈ centralizer ({t} : Set G)
        rw [mem_centralizer_singleton_iff]
        simpa [MulAut.conj_apply] using this.eq
    have : g * u' * g⁻¹ ∈ A := ⟨u', hu', by simp [MulAut.conj_apply]⟩
    exact hperfV A hAV hAperf this
  have hcomp : GLS.IsPCompIn 2 V Ωh := isPCompIn_of_normal_block hΩV hnorm hΩquasi
  have hlayer_t := barSub_le_layer_of_isPCompIn hx hxt hcomp
  have hΩt : Ωh ≤ centralizer ({t} : Set G) := fun a ha => (hΩV ha).2
  set χ : ↥Ωh →* CentralizerBar t := (proj t).comp (Subgroup.inclusion hΩt) with hχ
  have hχinj : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker with hk | hk
    · exact hk
    · exfalso
      have huh : ℓ u ∈ Ωh := ⟨u, hu, rfl⟩
      have hmem : (⟨ℓ u, huh⟩ : ↥Ωh) ∈ χ.ker := by rw [hk]; trivial
      have hu_ker : (⟨ℓ u, hΩt huh⟩ : ↥(centralizer ({t} : Set G))) ∈
          pPrimeCore 2 ↥(centralizer ({t} : Set G)) := (QuotientGroup.eq_one_iff _).1 hmem
      have hodd := orderOf_odd_of_mem_pPrimeCore hu_ker
      have hord2 : orderOf (⟨ℓ u, hΩt huh⟩ : ↥(centralizer ({t} : Set G))) = 2 := by
        rw [← Subgroup.orderOf_coe]
        change orderOf (ℓ u) = 2
        rw [orderOf_injective ℓ hℓinj]
        exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      rw [hord2] at hodd
      exact absurd hodd (by decide)
  have hrange : χ.range = S45.barSub t Ωh := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hΩt j.2) j.2
    · intro hy
      obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hy
      exact ⟨⟨g, hgJ⟩, rfl⟩
  let φ : ↥Ωh ≃* ↥(S45.barSub t Ωh) :=
    (MonoidHom.ofInjective hχinj).trans (MulEquiv.subgroupCongr hrange)
  have hxt2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  refine ⟨S45.barSub t Ωh, φ.symm.isSimpleGroup, ?_, hlayer_t, ?_, ?_⟩
  · rw [← Nat.card_congr φ.toEquiv, ← Nat.card_congr hΩeq.toEquiv]
    exact hcard''
  · intro a ha
    obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 ha
    rw [mem_centralizer_singleton_iff]
    have h1 : g * x = x * g := (mem_centralizer_singleton_iff.1 (hΩV hgJ).1)
    have h2 : (⟨g, hg⟩ : ↥(centralizer ({t} : Set G))) * ⟨x, hxt⟩ = ⟨x, hxt⟩ * ⟨g, hg⟩ :=
      Subtype.ext h1
    have h3 := congrArg (proj t) h2
    rwa [map_mul, map_mul] at h3
  · intro M hM hMc
    have h1 := perfect_le_barSub_resCent hxt hxt2 hM hMc
    have hres : resCent ({x, t} : Set G) ≤ Ωh := by
      refine hperfV _ ?_ (resCent_perfect _)
      intro a ha
      have hC := resCent_le ({x, t} : Set G) ha
      exact ⟨centralizer_le (Set.singleton_subset_iff.2 (by simp)) hC,
        centralizer_le (Set.singleton_subset_iff.2 (by simp)) hC⟩
    exact h1.trans (S45.barSub_mono hres)

theorem exotic_dvd (hExact : S1LiftExactProp)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) {q : ℕ} (hq1 : 1 < q)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hExo : IsExoticAutAt q α) {wK : ↥K} {w : G} (hwx : w ∈ centralizer ({x} : Set G)) {h : G}
    (hwK2 : wK * wK = 1) (hwKα : α wK = wK)
    (hwbar : barOf hwx = (wK : CentralizerBar x))
    (hh : h * w * h⁻¹ = w * v) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ q ^ 2 + 1) :
    r ∣ Nat.card ↥(layer (CentralizerBar w)) := by
  have hqodd := hExo.odd
  obtain ⟨t, ht⟩ : ∃ t : G, t = w * v := ⟨_, rfl⟩
  have htx : t ∈ centralizer ({x} : Set G) := by rw [ht]; exact Subgroup.mul_mem _ hwx hv
  have hxt : x ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 htx).symm
  obtain ⟨P, -, hPcard, hPlayer, -, -⟩ :=
    exotic_cmp hExact hset hfront e hq1 hv α hα hExo hwx hwK2 hwKα hwbar ht hxt
  have : Fact r.Prime := ⟨hr⟩
  have hdvd4 : r ∣ q ^ 4 - 1 := by
    have h1 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
      obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 :=
        ⟨q ^ 2 - 1, by have := Nat.one_le_pow 2 q (by omega); omega⟩
      have e : q ^ 4 = (a + 1) * (a + 1) := by rw [← ha]; ring
      rw [e, ha, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hrdvd _
  have hr2' : r ∣ Nat.card ↥P * 2 := by
    rw [hPcard]
    exact Dvd.dvd.mul_left hdvd4 _
  have hrP : r ∣ Nat.card ↥P := by
    rcases (Nat.Prime.dvd_mul hr).1 hr2' with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h) hr2
  have hrdvd_t : r ∣ Nat.card ↥(layer (CentralizerBar t)) :=
    hrP.trans (Subgroup.card_dvd_of_le hPlayer)
  have hht : h * w * h⁻¹ = t := by rw [hh, ht]
  subst hht
  have hlay := layer_map_mulEquiv' (barConj w h)
  have hcard : Nat.card ↥(layer (CentralizerBar (h * w * h⁻¹))) =
      Nat.card ↥(layer (CentralizerBar w)) := by
    rw [← hlay]
    exact Nat.card_congr ((layer (CentralizerBar w)).equivMapOfInjective _ (barConj w h).injective).toEquiv.symm
  rw [hcard] at hrdvd_t
  exact hrdvd_t

theorem exotic_contradiction (mo : ModelOps S) (hExact : S1LiftExactProp) (hno : S1LayerNoPrime)
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) (hfront : S1Front G x K)
    (e : ↥K ≃* ↥S) (ε : ℤ) {q : ℕ} (hmodel : IsSL4ModelAt ↥K ε q) (hq5 : 5 ≤ q)
    {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1)
    (hvK : barOf hv ∉ K) (α : MulAut ↥K)
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hExo : IsExoticAutAt q α) : False := by
  classical
  obtain ⟨wK, w, hwx, h, hwv, hwK2, hwK1, hwKz, hwKα, hw, hwbar, hh, hgrowth⟩ :=
    exotic_setup mo hExact hset hfront e hq5 hv hconj hvx hv2 hvK α hα hExo
  have hqodd := hExo.odd
  obtain ⟨r, hr, hr2, hrdvd⟩ := exists_odd_prime_dvd_sq_add_one hqodd hq5
  obtain ⟨hword, hwL, hwbarne⟩ := exotic_w_facts hExact hset hfront e hwx hwK2 hwK1 hwKz hw hwbar
  have hnoPrime : ¬ r ∣ Nat.card ↥(layer (CentralizerBar w)) :=
    hno G x K hset hfront ε q hmodel hq5 w hwx hword hwL hwbarne hgrowth r hr hr2 hrdvd
  exact hnoPrime (exotic_dvd hExact hset hfront e (by omega) hv α hα hExo hwx hwK2 hwKα hwbar hh hr hr2 hrdvd)

end CFSG.GH74.Generic.S1.Exo
