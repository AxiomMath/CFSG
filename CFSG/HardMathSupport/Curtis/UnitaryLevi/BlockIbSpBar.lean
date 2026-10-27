module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPrimeBar
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.AGLEmbedding.ParabAutIrr (map_perfectJoin_le)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

structure BlockBarData {X : Type*} [Group X] [Finite X] (J : Subgroup X) (v : X) : Prop where
  parab : ∃ T : Subgroup X, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set X) ≤ J
  ne_top : J ≠ ⊤
  cyc : CycPerfect 3 J
  pow : v ^ 3 = 1
  ne_one : v ≠ 1
  join : v ∈ perfectJoin J
  free : ∀ V : Subgroup X, V ≤ Subgroup.centralizer ({v} : Set X) → ⁅V, V⁆ = V → V = ⊥

section Central

variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X] {ψ : G →* X}

theorem blockBarData_of_central_quotient (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) {J : Subgroup G}
    (hpar : ∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set G) ≤ J)
    (htop : J ≠ ⊤) (hcyc : CycPerfect 3 J) {l : G} (hl3 : l ^ 3 = 1) (hl : l ∉ ψ.ker)
    (hlj : l ∈ perfectJoin J)
    (hfree : ∀ W : Subgroup G, ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({l} : Set G) → W = ⊥)
    (hodd : Odd (Nat.card ψ.ker)) :
    BlockBarData (J.map ψ) (ψ l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ⟩ := hpar
  have hkJ : ψ.ker ≤ J :=
    hker.trans ((Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)).trans hNJ)
  have hcomap : (J.map ψ).comap ψ = J := Subgroup.comap_map_eq_self hkJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hidx : ¬ 2 ∣ T.index := by
      have h := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
    let T' : Sylow 2 G := hT.2.1.toSylow hidx
    refine ⟨T.map ψ, ?_, ?_⟩
    · have := isSylowTwoOf_top_of_sylow' (T'.mapSurjective hψ)
      rwa [show ((T'.mapSurjective hψ : Sylow 2 X) : Subgroup X) = T.map ψ from
        Sylow.coe_mapSurjective hψ T'] at this
    · exact ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1 hNJ
  · intro h
    apply htop
    rw [← hcomap, h, Subgroup.comap_top]
  · intro V hVJ hV Q hQV hQp
    obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
      (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
    have hWJ : W ≤ J := by
      refine hWle.trans ?_
      rw [← hcomap]
      exact Subgroup.comap_mono hVJ
    have hPmap : (W ⊓ Q.comap ψ).map ψ = Q := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        have hyV : y ∈ W.map ψ := by rw [hWmap]; exact hQV hy
        obtain ⟨w, hw, rfl⟩ := hyV
        exact ⟨w, ⟨hw, hy⟩, rfl⟩
    obtain ⟨R, hRP, hRp, hRmap⟩ := exists_pSubgroup_map_eq Nat.prime_three hPmap hQp
    have hRW : R ≤ W := fun x hx => (hRP hx).1
    have hRcyc : IsCyclic R := hcyc W hWJ hW R hRW hRp
    subst hRmap
    have := hRcyc
    exact isCyclic_of_surjective (ψ.subgroupMap R) (ψ.subgroupMap_surjective R)
  · rw [← map_pow, hl3, map_one]
  · intro h
    exact hl (MonoidHom.mem_ker.2 h)
  · exact map_perfectJoin_le ψ le_rfl ⟨l, hlj, rfl⟩
  · intro V hVC hV
    obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
      (by rw [MonoidHom.range_eq_top.2 hψ]; exact le_top)
    have hcentral : ∀ w ∈ W, ⁅w, l⁆ ∈ Subgroup.center G := by
      intro w hw
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      have hwV : ψ w ∈ V := by rw [← hWmap]; exact ⟨w, hw, rfl⟩
      exact (Subgroup.mem_centralizer_iff.1 (hVC hwV) (ψ l) (Set.mem_singleton _)).symm
    have hWC : W ≤ Subgroup.centralizer ({l} : Set G) := by
      rw [← hW]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := commutator_commutator_eq_one_of_central (hcentral a ha) (hcentral b hb)
      rw [commutatorElement_eq_one_iff_commute] at h1
      exact h1.symm
    have := hfree W hW hWC
    rw [← hWmap, this, Subgroup.map_bot]

end Central

section Equiv

variable {X X' : Type*} [Group X] [Group X']

theorem BlockBarData.map_mulEquiv [Finite X] [Finite X'] (e : X ≃* X') {J : Subgroup X} {v : X}
    (h : BlockBarData J v) : BlockBarData (J.map e.toMonoidHom) (e v) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT, hNJ⟩ := h.parab
    refine ⟨T.map e.toMonoidHom, ⟨le_top, hT.2.1.map _, ?_⟩, ?_⟩
    · have h2 := hT.2.2
      have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
      have e2 : ((T.map e.toMonoidHom).subgroupOf ⊤).index = (T.map e.toMonoidHom).index :=
        Subgroup.relIndex_top_right _
      rw [e2, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective T]
      rwa [e1] at h2
    · rw [← Subgroup.map_normalizer_eq_of_bijective (T : Subgroup X) e.bijective]
      exact Subgroup.map_mono hNJ
  · intro htop
    apply h.ne_top
    apply Subgroup.map_injective hinj
    rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
  · intro V hVJ hV Q hQV hQp
    have hV' : V.map e.symm.toMonoidHom ≤ J := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hVJ hy
      simpa using hz
    have hVp : ⁅V.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom⁆ = V.map e.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hV]
    have hQ' : Q.map e.symm.toMonoidHom ≤ V.map e.symm.toMonoidHom := Subgroup.map_mono hQV
    have := h.cyc _ hV' hVp _ hQ' (hQp.map _)
    have hQeq := map_map_symm e Q
    rw [← hQeq]
    exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap _)
      (e.toMonoidHom.subgroupMap_surjective _)
  · rw [← map_pow, h.pow, map_one]
  · intro h1
    apply h.ne_one
    exact e.injective (by rw [map_one]; exact h1)
  · rw [← map_perfectJoin_mulEquiv e J]
    exact ⟨v, h.join, rfl⟩
  · intro V hVC hV
    have hVc : V.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({v} : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have := Subgroup.mem_centralizer_iff.1 (hVC hy) (e g) (by simp)
      apply e.injective
      simpa using this
    have hVp : ⁅V.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom⁆ = V.map e.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hV]
    have := h.free _ hVc hVp
    rw [← map_map_symm e V, this, Subgroup.map_bot]

end Equiv

section Data

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

omit [Finite Y] in
private theorem le_normalizer_cent (Lb : Subgroup Y) :
    Lb ≤ Subgroup.normalizer (Subgroup.centralizer (Lb : Set Y) : Set Y) := by
  have key : ∀ g ∈ Lb, ∀ c, c ∈ Subgroup.centralizer (Lb : Set Y) → g * c * g⁻¹ ∈
      Subgroup.centralizer (Lb : Set Y) := by
    intro g hg c hc
    have : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc g hg]; group
    rwa [this]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (Lb.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem exists_mem_perfectJoin_mul (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) :
    ∃ p ∈ perfectJoin Pb, ∃ c ∈ Subgroup.centralizer (Lb : Set Y), x = p * c := by
  have hPL : Pb ≤ Lb := hP.parab.1
  set C : Subgroup Y := Subgroup.centralizer (Lb : Set Y) with hC
  have hcomm : ∀ a ∈ Pb, ∀ c ∈ C, a * c = c * a :=
    fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc a (hPL ha)
  set Q : Subgroup Y := Pb ⊔ C with hQ
  have hPQ : Pb ≤ Q := le_sup_left
  have hCQ : C ≤ Q := le_sup_right
  have hQn : Q ≤ Subgroup.normalizer (C : Set Y) :=
    sup_le ((le_normalizer_cent Lb).trans' hPL) Subgroup.le_normalizer
  have : (C.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).mpr hQn
  let π : ↥Pb →* ↥Q ⧸ C.subgroupOf Q :=
    (QuotientGroup.mk' (C.subgroupOf Q)).comp (Subgroup.inclusion hPQ)
  have hker : π.ker ≤ Subgroup.center ↥Pb := by
    intro p hp
    have h1 : (p : Y) ∈ C := by
      have : Subgroup.inclusion hPQ p ∈ C.subgroupOf Q := by
        rw [← QuotientGroup.ker_mk' (C.subgroupOf Q)]
        exact hp
      exact this
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 (q : Y) (hPL q.2))
  have hsurj : Function.Surjective π := by
    rintro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) q
    obtain ⟨a, ha, c, hc, hac⟩ := exists_mul_of_mem_sup_of_commute hcomm n.2
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hPQ ⟨a, ha⟩) = QuotientGroup.mk n
    rw [QuotientGroup.eq]
    show (Subgroup.inclusion hPQ ⟨a, ha⟩)⁻¹ * n ∈ C.subgroupOf Q
    rw [Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hPQ ⟨a, ha⟩)⁻¹ * n : Q).1 = a⁻¹ * (n : Y) := rfl
    show ((Subgroup.inclusion hPQ ⟨a, ha⟩)⁻¹ * n : Q).1 ∈ C
    rw [this, hac]
    simpa using hc
  set D' : Subgroup ↥Q := D.subgroupOf Q with hD'
  have hD'p : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_commutator, hD', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD.Dle,
      hD.Dperf]
  set Dbar : Subgroup (↥Q ⧸ C.subgroupOf Q) := D'.map (QuotientGroup.mk' (C.subgroupOf Q)) with hDbar
  have hDbarp : ⁅Dbar, Dbar⁆ = Dbar := by rw [hDbar, ← Subgroup.map_commutator, hD'p]
  obtain ⟨W, hW, -, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq π hker hDbarp
    (by rw [MonoidHom.range_eq_top.2 hsurj]; exact le_top)
  have hxQ : x ∈ Q := hD.Dle hD.hx
  have hxD : (⟨x, hxQ⟩ : ↥Q) ∈ D' := hD.hx
  have hmem : QuotientGroup.mk' (C.subgroupOf Q) ⟨x, hxQ⟩ ∈ W.map π := by
    rw [hWmap]; exact ⟨_, hxD, rfl⟩
  obtain ⟨w, hw, hwx⟩ := hmem
  have hq : (Subgroup.inclusion hPQ w)⁻¹ * ⟨x, hxQ⟩ ∈ C.subgroupOf Q := by
    have := hwx
    change QuotientGroup.mk (Subgroup.inclusion hPQ w) = QuotientGroup.mk ⟨x, hxQ⟩ at this
    rw [QuotientGroup.eq] at this
    exact this
  have hc : (w : Y)⁻¹ * x ∈ C := by
    have := Subgroup.mem_subgroupOf.mp hq
    exact this
  refine ⟨(w : Y), ?_, (w : Y)⁻¹ * x, hc, by simp⟩
  have hWp : ⁅W.map Pb.subtype, W.map Pb.subtype⁆ = W.map Pb.subtype := by
    rw [← Subgroup.map_commutator, hW]
  exact le_perfectJoin (by rintro _ ⟨y, -, rfl⟩; exact y.2) hWp ⟨w, hw, rfl⟩

theorem exists_inner_three_join (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) :
    ∃ u ∈ perfectJoin Pb, u ^ 3 = 1 ∧ u ∉ Subgroup.centralizer (Lb : Set Y) ∧
      ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({u} : Set Y) →
        W = ⊥ := by
  have hPL : Pb ≤ Lb := hP.parab.1
  obtain ⟨p, hpj, c, hc, hxpc⟩ := exists_mem_perfectJoin_mul hP hD
  have hp : p ∈ Pb := perfectJoin_le Pb hpj
  have hp3 : p ^ 3 * c ^ 3 = 1 := by
    have hpc : Commute p c := Subgroup.mem_centralizer_iff.mp hc p (hPL hp)
    rw [← hpc.mul_pow, ← hxpc]; exact hD.hx3
  have hz : p ^ 3 ∈ Subgroup.centralizer (Lb : Set Y) := by
    have : p ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hp3
    rw [this]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)
  have hzL : p ^ 3 ∈ Lb := Lb.pow_mem (hPL hp) 3
  have hn3 : Nat.Coprime 3 (orderOf (p ^ 3)) := by
    have hmem : (⟨p ^ 3, hzL⟩ : Lb) ∈ Subgroup.center Lb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz g.1 g.2)
    have h1 : orderOf (⟨⟨p ^ 3, hzL⟩, hmem⟩ : Subgroup.center Lb) ∣
        Nat.card (Subgroup.center Lb) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨⟨p ^ 3, hzL⟩, hmem⟩ : Subgroup.center Lb) = orderOf (p ^ 3) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact Nat.Coprime.coprime_dvd_right (h2 ▸ h1) hD.cop
  generalize hn : orderOf (p ^ 3) = n at hn3
  have hn1 : (p ^ 3) ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  have hmod : n * n % 3 = 1 := by
    have h0 : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hn3
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hxm : x ^ (n * n) = x := by
    generalize n * n = m at hmod
    obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
    rw [pow_succ, pow_mul, hD.hx3, one_pow, one_mul]
  have hactp : Lift.Act Lb x p := by
    intro l hl
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
    rw [hxpc]
    calc p * c * l * (p * c)⁻¹ = p * (c * l) * c⁻¹ * p⁻¹ := by group
      _ = p * (l * c) * c⁻¹ * p⁻¹ := by rw [hcl]
      _ = p * l * p⁻¹ := by group
  have hactu : Lift.Act Lb x (p ^ (n * n)) := by
    have := Lift.act_pow (hPL hp) hactp (n * n)
    rwa [hxm] at this
  have hu3 : (p ^ (n * n)) ^ 3 = 1 := by
    calc (p ^ (n * n)) ^ 3 = ((p ^ 3) ^ n) ^ n := by
          simp only [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hn1, one_pow]
  refine ⟨p ^ (n * n), Subgroup.pow_mem _ hpj _, hu3, ?_, ?_⟩
  · intro hu
    apply hD.hxC
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hactu l hl
    have h2 : p ^ (n * n) * l * (p ^ (n * n))⁻¹ = l := by
      rw [← (Subgroup.mem_centralizer_iff.mp hu l hl)]; group
    rw [h2] at h1
    calc l * x = (x * l * x⁻¹) * x := by rw [h1]
      _ = x * l := by group
  · intro W hW hWp hWc
    refine hD.free W hW hWp fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 := hactu w (hW hw)
    have h2 := Subgroup.mem_centralizer_iff.mp (hWc hw) _ (Set.mem_singleton _)
    have h3 : x * w * x⁻¹ = w := by
      rw [h1, h2]; group
    calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [h3]

theorem exists_blockBar (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) {X : Type}
    [Group X] [Finite X] (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* X) :
    ∃ v : X, BlockBarData ((Pb.subgroupOf Lb).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb)))) v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : Pb ≤ Lb := hP.parab.1
  obtain ⟨u, huj, hu3, huC, hufree⟩ := exists_inner_three_join hP hD
  have huP : u ∈ Pb := perfectJoin_le Pb huj
  set ψ : ↥Lb →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb)) with hψ
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center ↥Lb := by
    ext g
    rw [MonoidHom.mem_ker, ← QuotientGroup.ker_mk' (Subgroup.center ↥Lb), MonoidHom.mem_ker]
    simp only [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => e.injective (h.trans (map_one e).symm), fun h => by rw [h, map_one]⟩
  set l : ↥Lb := ⟨u, hPL huP⟩ with hl
  refine ⟨ψ l, ?_⟩
  refine blockBarData_of_central_quotient (G := ↥Lb) (J := Pb.subgroupOf Lb) (l := l) hψsurj
    (by rw [hψker]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP.parab
    refine ⟨T.subgroupOf Lb, ⟨le_top, hT2.comap_subtype (K := Lb), ?_⟩, ?_⟩
    · have e : ((T.subgroupOf Lb).subgroupOf ⊤).index = (T.subgroupOf Lb).index :=
        Subgroup.relIndex_top_right _
      rw [e]
      exact hTi
    · intro y hy
      rw [Subgroup.mem_subgroupOf]
      refine hNJ ⟨y.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
      have h1 : (⟨t, hTL ht⟩ : ↥Lb) ∈ T.subgroupOf Lb := Subgroup.mem_subgroupOf.2 ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hy ⟨t, hTL ht⟩).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
  · intro hJt
    apply hP.ne
    refine le_antisymm hPL (fun y hy => ?_)
    have := (Subgroup.eq_top_iff' _).1 hJt ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro V hVJ hV Q hQV hQp
    have hV' : ⁅V.map Lb.subtype, V.map Lb.subtype⁆ = V.map Lb.subtype := by
      rw [← Subgroup.map_commutator, hV]
    have hVJ' : V.map Lb.subtype ≤ Pb := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hVJ hy)
    have : IsCyclic ↥(Q.map Lb.subtype) := hD.cyc (V.map Lb.subtype) hVJ' hV' (Q.map Lb.subtype)
      (Subgroup.map_mono hQV) (hQp.map Lb.subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q Lb.subtype Lb.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  · exact Subtype.ext (by simpa [hl] using hu3)
  · rw [hψker]
    intro hz
    apply huC
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
    exact congrArg Subtype.val this
  · exact mem_perfectJoin_subgroupOf (hPL huP) hPL huj
  · intro W hW hWc
    have hW' : ⁅W.map Lb.subtype, W.map Lb.subtype⁆ = W.map Lb.subtype := by
      rw [← Subgroup.map_commutator, hW]
    have h := hufree (W.map Lb.subtype) (by rintro _ ⟨w, -, rfl⟩; exact w.2) hW' (by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hWc hw)))
    rw [eq_bot_iff]
    intro w hw
    have : (w : Y) ∈ W.map Lb.subtype := ⟨w, hw, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · rw [hψker]; exact hP.odd

end Data

end CFSG.HardMathSupport.Curtis.UnitaryLevi
