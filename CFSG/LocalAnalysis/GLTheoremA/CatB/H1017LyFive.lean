module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Ly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.SignalizerFunctor.Helpers

section Generic

variable {X : Type} [Group X] [Finite X]

theorem exists_hyperplane_fixed_p {p : ℕ} (hp : p.Prime) {E Q : Subgroup X} (hE : IsElemAbelian p E) (hEne : E ≠ ⊥)
    (hQ : ¬ p ∣ Nat.card Q) (hQne : Q ≠ ⊥) (hEQ : E ≤ Subgroup.normalizer (Q : Set X)) :
    ∃ B : Subgroup E, B.index = p ∧ ∃ x ∈ Q, x ≠ 1 ∧ ∀ b ∈ B, (b : X) * x = x * b := by
  have : Fact p.Prime := ⟨hp⟩
  have : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun e =>
        Subtype.ext (by simpa using hE.2 e e.2) }
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  let _ := conjugationAction E Q hEQ
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := Q) hQ
  by_contra hcon
  push Not at hcon
  have hbot : (⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B Q) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB y hy => ?_)
    rw [Subgroup.mem_bot]
    by_contra hy1
    obtain ⟨b, hbB, hb⟩ := hcon B hB y y.2 (fun h => hy1 (Subtype.ext h))
    apply hb
    have h := congrArg Subtype.val (hy ⟨b, hbB⟩)
    change (b : X) * (y : X) * (b : X)⁻¹ = y at h
    calc (b : X) * y = (b : X) * y * (b : X)⁻¹ * b := by group
      _ = y * b := by rw [h]
  rw [hbot] at hgen
  apply hQne
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : Q) ∈ (⊥ : Subgroup Q) := hgen ▸ Subgroup.mem_top _
  simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)


theorem card_le_of_involution_data_pk {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ)
    (ha : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X,
      F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian p F → Nat.card F ≤ p ^ k)
    (hb : ∀ t : X, orderOf t = 2 → ∀ F : Subgroup X,
      F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian p F → Nat.card F = p ^ k →
      ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) → u * t = t * u → u = t)
    (R E : Subgroup X) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set X)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hlt
    exact absurd hlt (not_lt.2 (Nat.one_le_pow _ _ hp.pos))
  have hR3 : ¬ p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR2
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨B, hB, x, hxR, hx1, hBx⟩ := exists_hyperplane_fixed_p hp hE hEne hR3 hR hER
  set F : Subgroup X := B.map E.subtype with hFdef
  have hFE : F ≤ E := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hFab : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE
  have hFcard : Nat.card F * p = Nat.card E := by
    rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective, ← hB]
    exact Subgroup.card_mul_index B
  set V : Subgroup X := R ⊓ Subgroup.centralizer (F : Set X) with hVdef
  have hxV : x ∈ V := by
    refine ⟨hxR, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hBx b hb
  have hV2 : IsPGroup 2 V := hR2.to_le inf_le_left
  haveI : Nontrivial V := ⟨⟨⟨x, hxV⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hZ := hV2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center V) 2
    (by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hV2.to_subgroup (Subgroup.center V))
      have hn1 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ ((Subgroup.eq_bot_iff_card _).2 hn)
      rw [hn]
      exact dvd_pow_self 2 hn1)
  set u : X := ((z : V) : X) with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have huV : u ∈ V := (z : V).2
  have hucent : ∀ w ∈ V, u * w = w * u := fun w hw => by
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨w, hw⟩)
    simpa [hudef] using this.symm
  have hFu : F ≤ Subgroup.centralizer ({u} : Set X) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 huV.2) f hf)
  have hFk : Nat.card F = p ^ k := by
    have h1 := ha u hu2 F hFu hFab
    have hF3 : IsPGroup p F := fun g => ⟨1, Subtype.ext (by simpa using hFab.2 g g.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hF3
    rw [hm] at h1 hFcard ⊢
    have hmk : m ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have h2 : p ^ k < p ^ (m + 1) := by rw [pow_succ, hFcard]; exact hlt
    have hkm : k < m + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h2
    have : m = k := by omega
    rw [this]
  obtain ⟨e, heE, heF⟩ : ∃ e ∈ E, e ∉ F := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ F := hcon
    have := Subgroup.card_le_of_le hle
    omega
  have hfe : ∀ f ∈ F, f * e = e * f := fun f hf => comm_of_elemAbelian hE (hFE hf) heE
  set v : X := e * u * e⁻¹ with hvdef
  have hvR : v ∈ R := (Subgroup.le_normalizer_iff.mp hER) e heE u huV.1
  have hvC : v ∈ Subgroup.centralizer (F : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfu : f * u = u * f := (Subgroup.mem_centralizer_iff.1 huV.2) f hf
    have h1 : f * e⁻¹ = e⁻¹ * f := by
      calc f * e⁻¹ = e⁻¹ * (e * f) * e⁻¹ := by group
        _ = e⁻¹ * (f * e) * e⁻¹ := by rw [hfe f hf]
        _ = e⁻¹ * f := by group
    calc f * v = (f * e) * u * e⁻¹ := by rw [hvdef]; group
      _ = e * (f * u) * e⁻¹ := by rw [hfe f hf]; group
      _ = e * u * (f * e⁻¹) := by rw [hfu]; group
      _ = v * f := by rw [h1, hvdef]; group
  have hvV : v ∈ V := ⟨hvR, hvC⟩
  have hv2 : orderOf v = 2 := by
    rw [hvdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu2]
  have huv : v * u = u * v := (hucent v hvV).symm
  by_cases hvu : v = u
  · have heu : e ∈ Subgroup.centralizer ({u} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : e * u * e⁻¹ = u := hvu
      calc e * u = e * u * e⁻¹ * e := by group
        _ = u * e := by rw [this]
    set E₂ : Subgroup X := F ⊔ Subgroup.zpowers e
    have hE₂E : E₂ ≤ E := sup_le hFE ((Subgroup.zpowers_le).2 heE)
    have hE₂u : E₂ ≤ Subgroup.centralizer ({u} : Set X) := sup_le hFu ((Subgroup.zpowers_le).2 heu)
    have hFE₂ : F < E₂ := lt_of_le_of_ne le_sup_left fun h =>
      heF (h ▸ (le_sup_right : Subgroup.zpowers e ≤ E₂) (Subgroup.mem_zpowers e))
    have h1 := ha u hu2 E₂ hE₂u (CFSG.Open.IsElemAbelian.mono hE hE₂E)
    have h2 := Subgroup.card_lt_of_lt hFE₂
    omega
  · exact hvu (hb u hu2 F hFu hFab hFk v hv2 hvC huv)

end Generic

section Alt

open Equiv Equiv.Perm

theorem not_dvd_card_centralizer_of_even_involution_five {σ : Perm (Fin 11)} (h2 : orderOf σ = 2)
    (hs : Perm.sign σ = 1) :
    ¬ 25 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 11)))) := by
  rw [Perm.nat_card_centralizer]
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [h2]; exact Nat.prime_two)
  rw [h2] at hn
  have hsum := Perm.sum_cycleType_le σ
  have hsign := Perm.sign_of_cycleType σ
  rw [hn] at hsum hsign ⊢
  rw [hs] at hsign
  simp only [Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn4 : n ≤ 4 := by omega
  interval_cases n <;> first | exact absurd hsign (by decide) | decide

end Alt

section Ly

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem injective_of_center_two_five {C : Type} [Group C] [Finite C]
    (hZ : Nat.card (Subgroup.center C) = 2)
    {P : Type} [Group P] (φ : C →* P) (hker : φ.ker ≤ Subgroup.center C) {F : Subgroup C}
    (hF : IsElemAbelian 5 F) : Function.Injective (φ.comp F.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have hxZ : (x : C) ∈ Subgroup.center C := hker hx
  have h2 : (x : C) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center C) (x := ⟨x, hxZ⟩)
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  have h3 : (x : C) ^ 5 = 1 := hF.2 x x.2
  have : (x : C) = 1 := by
    calc (x : C) = (x : C) ^ 5 * ((x : C) ^ 2)⁻¹ * ((x : C) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; group
  rw [Subgroup.mem_bot]
  exact Subtype.ext this

theorem isElemAbelian_range_five {A P : Type} [Group A] [Group P] (ψ : A →* P)
    (hA : ∀ a b : A, a * b = b * a) (h3 : ∀ a : A, a ^ 5 = 1) : IsElemAbelian 5 ψ.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a, x, rfl⟩ := a
    obtain ⟨b, y, rfl⟩ := b
    show ψ x * ψ y = ψ y * ψ x
    rw [← map_mul, ← map_mul, hA]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, h3, map_one]

theorem ly_involution_data_five {K : Type} [Group K] [Finite K] (hK : IsSporadic K .Ly) {t : K}
    (ht : orderOf t = 2) :
    (∀ F : Subgroup K, F ≤ Subgroup.centralizer ({t} : Set K) → IsElemAbelian 5 F →
      Nat.card F ≤ 5 ^ 2) ∧
    (∀ F : Subgroup K, F ≤ Subgroup.centralizer ({t} : Set K) → IsElemAbelian 5 F →
      Nat.card F = 5 ^ 2 → ∀ u : K, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set K) →
        u * t = t * u → u = t) := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := CFSG.EvenSporadicStandard.LyStd.isDoubleCoverOfAlt_ly hK ht
  set C := Subgroup.centralizer ({t} : Set K) with hCdef
  let φ : ↥C →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥C)))
  have hker : φ.ker ≤ Subgroup.center ↥C := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
    have h2 : (QuotientGroup.mk x : ↥C ⧸ Subgroup.center ↥C) = 1 := by
      rw [← map_one e.symm, ← h1, MulEquiv.symm_apply_apply]
    exact (QuotientGroup.eq_one_iff x).1 h2
  have hdata : ∀ F : Subgroup K, F ≤ C → IsElemAbelian 5 F →
      IsElemAbelian 5 ((φ.comp (F.subgroupOf C).subtype).range) ∧
        Nat.card ((φ.comp (F.subgroupOf C).subtype).range) = Nat.card F := by
    intro F hFC hF
    have hF' : IsElemAbelian 5 (F.subgroupOf C) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · exact comm_of_elemAbelian hF a.2 b.2
      · exact hF.2 _ hx
    have hinj := injective_of_center_two_five hZ φ hker hF'
    refine ⟨isElemAbelian_range_five _ (fun a b => Subtype.ext (Subtype.ext
      (comm_of_elemAbelian hF a.2 b.2))) (fun a => Subtype.ext (Subtype.ext (hF.2 _ a.2))), ?_⟩
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
  refine ⟨fun F hFC hF => ?_, fun F hFC hF hF25 u hu hufF hut => ?_⟩
  · obtain ⟨hE, hc⟩ := hdata F hFC hF
    rw [← hc]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltInputs.card_le_pow_div hE
  · by_contra hne
    have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hut
    have htZ : (⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
    set ū : Equiv.Perm (Fin 11) := φ ⟨u, huC⟩ with hū
    have hū1 : ū ≠ 1 := by
      intro h1
      have huZ : (⟨u, huC⟩ : ↥C) ∈ Subgroup.center ↥C := hker h1
      classical
      haveI : Fintype ↥(Subgroup.center ↥C) := Fintype.ofFinite _
      have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; norm_num at ht
      have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; norm_num at hu
      let zt : ↥(Subgroup.center ↥C) := ⟨_, htZ⟩
      let zu : ↥(Subgroup.center ↥C) := ⟨_, huZ⟩
      have hcard := Finset.card_le_univ ({1, zt, zu} : Finset ↥(Subgroup.center ↥C))
      rw [← Nat.card_eq_fintype_card, hZ] at hcard
      rw [Finset.card_insert_of_notMem, Finset.card_pair] at hcard
      · omega
      · intro h
        exact hne (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ht1 (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm,
          fun h => hu1 (congrArg (fun z : ↥(Subgroup.center ↥C) => ((z : ↥C) : K)) h).symm⟩
    have hū2 : orderOf ū = 2 := by
      refine orderOf_eq_prime ?_ hū1
      rw [hū, ← map_pow]
      have : (⟨u, huC⟩ : ↥C) ^ 2 = 1 := Subtype.ext (by
        have := pow_orderOf_eq_one u
        rwa [hu] at this)
      rw [this, map_one]
    have hūs : Equiv.Perm.sign ū = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (e (QuotientGroup.mk ⟨u, huC⟩)).2
    obtain ⟨-, hc⟩ := hdata F hFC hF
    have hle : (φ.comp (F.subgroupOf C).subtype).range ≤
        Subgroup.centralizer ({ū} : Set (Equiv.Perm (Fin 11))) := by
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hū, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show ((x : ↥C) : K) * u = u * ((x : ↥C) : K)
      exact (Subgroup.mem_centralizer_iff.1 hufF) _ (Subgroup.mem_subgroupOf.1 x.2)
    have h25 := Subgroup.card_dvd_of_le hle
    rw [hc, hF25] at h25
    exact not_dvd_card_centralizer_of_even_involution_five hū2 hūs h25

theorem twoRankLe_five_ly : TwoRankLe 5 .Ly 2 := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ly
  have hK : IsSporadic K .Ly := ⟨e.trans b.symm⟩
  refine CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le (by norm_num)
    fun R E hR hR2 hEN hE => ?_
  exact card_le_of_involution_data_pk (by norm_num) (by norm_num) 2
    (fun t ht => (ly_involution_data_five hK ht).1)
    (fun t ht => (ly_involution_data_five hK ht).2) R E hR hR2 hEN hE

end Ly

end CFSG.LocalAnalysis.GLTheoremA.H1017
