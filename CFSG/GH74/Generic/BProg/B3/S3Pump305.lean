module

public import CFSG.GH74.Generic.BProg.B3.S3Pump304

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump305

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_pLayerOf {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((pLayerOf 2 X : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (X : Set G) →
      (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom ≤ pLayerOf 2 X := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hX : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have h := Stage1.Thm2.Recip.isPCompIn_map_conj hK g
    rw [hX] at h
    exact le_sSup h
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    simpa [MulAut.conj_apply] using key hg h1
  · intro hz
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * z * g⁻¹) ∈
        (pLayerOf 2 X).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hz
    have h2 := key (inv_mem hg) h1
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem inf_pPrimeCoreOf_le {L M : Subgroup G} (hLM : L ≤ M) :
    L ⊓ pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥L := (pPrimeCoreOf 2 M).subgroupOf L
  have hNnorm : N.Normal := by
    refine ⟨fun n hn l => ?_⟩
    have hlM' : (l : G) ∈ normalizer (M : Set G) := Subgroup.le_normalizer (hLM l.2)
    have hlO : (l : G) ∈ normalizer (pPrimeCoreOf 2 M : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf hlM'
    have hn' : (n : G) ∈ pPrimeCoreOf 2 M := hn
    show (l : G) * (n : G) * (l : G)⁻¹ ∈ pPrimeCoreOf 2 M
    exact (mem_normalizer_iff.mp hlO _).mp hn'
  have hNodd : Odd (Nat.card ↥N) := by
    have h1 : Nat.card ↥(N.map L.subtype) = Nat.card ↥N :=
      Subgroup.card_map_of_injective L.subtype_injective
    have h2 : N.map L.subtype ≤ pPrimeCoreOf 2 M := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h3 : Nat.card ↥(N.map L.subtype) ∣ Nat.card ↥(pPrimeCoreOf 2 M) :=
      Subgroup.card_dvd_of_le h2
    rw [h1] at h3
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) h3
  have hNle : N ≤ pPrimeCore 2 ↥L :=
    le_sSup ⟨hNnorm, Nat.coprime_two_left.2 hNodd⟩
  intro m hm
  obtain ⟨hmL, hmO⟩ := Subgroup.mem_inf.1 hm
  exact ⟨⟨m, hmL⟩, hNle hmO, rfl⟩

theorem pLayerOf_self {X K : Subgroup G} (hK : IsPCompIn 2 X K) : pLayerOf 2 K = K :=
  le_antisymm (sSup_le fun _ hL => hL.1) (le_sSup (Lemma212Aux.isPCompIn_of_le hK le_rfl hK.1))

omit [Finite G] in
theorem eq_of_mul_odd {y o u : G} (hy2 : y * y = 1) (hodd : Odd (orderOf o)) (hu : u = o * y)
    (hu2 : u * u = 1) (hc : u * y = y * u) : u = y := by
  have ho : o = u * y := by rw [hu, mul_assoc, hy2, mul_one]
  have ho2 : o * o = 1 := by
    calc o * o = (u * y) * (u * y) := by rw [← ho]
      _ = u * (y * u) * y := by group
      _ = u * (u * y) * y := by rw [← hc]
      _ = (u * u) * (y * y) := by group
      _ = 1 := by rw [hu2, hy2, one_mul]
  have hdvd : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have h1 : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have : o = 1 := orderOf_eq_one_iff.1 h1
  rw [hu, this, one_mul]

section Main

variable {x y : G} {K A T : Subgroup G}

theorem le_pumpUp (h : Setup30 G x K A y) : Ly K y ≤ pumpUp 2 (Ly K y) y := by
  have hL := (Setup30.layer h).1
  have hLC : Ly K y ≤ centralizer ({y} : Set G) := (hL.1.trans inf_le_right)
  have hself : pLayerOf 2 (Ly K y) = Ly K y := pLayerOf_self hL
  rw [TwoThin.pumpUp_eq_map_pumpupY]
  intro z hz
  refine ⟨⟨z, hLC hz⟩, TwoThin.subset_pumpupY _ ?_, rfl⟩
  show z ∈ pLayerOf 2 (Ly K y ⊓ centralizer ({y} : Set G))
  rw [inf_of_le_left hLC, hself]
  exact hz

theorem conj_mem_pumpUp (h : Setup30 G x K A y)
    (hlayerU : pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) = Ly K y)
    {g : G} (hg : g ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) :
    ∀ z ∈ pumpUp 2 (Ly K y) y, g * z * g⁻¹ ∈ pumpUp 2 (Ly K y) y := by
  have hL := (Setup30.layer h).1
  have hLC : Ly K y ≤ centralizer ({y} : Set G) := (hL.1.trans inf_le_right)
  have hself : pLayerOf 2 (Ly K y) = Ly K y := pLayerOf_self hL
  have hgL : g ∈ normalizer ((Ly K y : Subgroup G) : Set G) := by
    rw [← hlayerU]
    exact mem_normalizer_pLayerOf (Subgroup.le_normalizer hg)
  have hgC : g ∈ centralizer ({y} : Set G) := hg.2
  set Λ : Subgroup ↥(centralizer ({y} : Set G)) :=
    (pLayerOf 2 (Ly K y ⊓ centralizer ({y} : Set G))).subgroupOf (centralizer ({y} : Set G)) with hΛ
  have hΛmem : ∀ a : ↥(centralizer ({y} : Set G)), a ∈ Λ ↔ (a : G) ∈ Ly K y := by
    intro a
    rw [hΛ, Subgroup.mem_subgroupOf, inf_of_le_left hLC, hself]
  have hs := TwoThin.map_conj_pumpupY_le_of_map_le Λ (s := ⟨g, hgC⟩) (by
    intro a ha
    rw [hΛmem] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp hgL _).mp ha)
  intro z hz
  rw [TwoThin.pumpUp_eq_map_pumpupY] at hz ⊢
  obtain ⟨j, hj, rfl⟩ := hz
  exact ⟨_, hs ⟨j, hj, rfl⟩, rfl⟩

theorem pLayer_C0_eq_bot (h : Setup30 G x K A y)
    (hlayerU : pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) = Ly K y) :
    pLayerOf 2 (CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := pumpUp 2 (Ly K y) y with hH
  set U : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hU
  set Y0 : Subgroup G := CxK y H ⊓ centralizer ({x} : Set G) with hY0
  have hY0U : Y0 ≤ U := fun g hg => ⟨hg.2, hg.1.1⟩
  have hmH : ∀ g ∈ U, g ∈ normalizer (H : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨conj_mem_pumpUp h hlayerU hg z, fun hz => ?_⟩
    have := conj_mem_pumpUp h hlayerU (inv_mem hg) _ hz
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [e] at this
  have hconj : ∀ g ∈ U, ∀ c ∈ Y0, g * c * g⁻¹ ∈ Y0 := by
    intro g hg c hc
    obtain ⟨⟨hcy, hcs⟩, hcx⟩ := hc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.2 hcy) (Subgroup.inv_mem _ hg.2)
    · exact Obs.conj_mem_centralizerSection (hmH g hg)
        (TwoThin.mem_normalizer_pPrimeCoreOf (hmH g hg)) hcs
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.1 hcx) (Subgroup.inv_mem _ hg.1)
  have hUn : U ≤ normalizer (Y0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconj g hg c hc, fun hc => ?_⟩
    have := hconj g⁻¹ (inv_mem hg) _ hc
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rwa [e] at this
  have hsub : (Y0.subgroupOf U).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hY0U).mpr hUn).isSubnormal
  refine le_bot_iff.1 (sSup_le fun J hJ => ?_)
  have hJU : IsPCompIn 2 U J := B1.isPCompIn_of_isSubnormal 2 hY0U hsub hJ
  have hJL : J ≤ Ly K y := hlayerU ▸ le_sSup hJU
  have hJH : J ≤ H := hJL.trans (le_pumpUp h)
  have hJperf : ⁅J, J⁆ = J :=
    TwoThin.commutator_self_of_isTwoComponent hJ.1 (TwoThin.isPCompIn_two_iff.mp hJ).2
  have hJO : J ≤ pPrimeCoreOf 2 H := by
    calc J = ⁅J, J⁆ := hJperf.symm
      _ ≤ pPrimeCoreOf 2 H := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        obtain ⟨⟨-, ⟨-, -, hbc⟩⟩, -⟩ := hJ.1 hb
        exact hbc a (hJH ha)
  have hodd : Odd (Nat.card ↥J) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd H) (Subgroup.card_dvd_of_le hJO)
  exact (eq_bot_of_perfect_of_odd hJperf hodd).le

theorem invol_C0 (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hlayerU : pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) = Ly K y) :
    ∀ u ∈ CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G), u * u = 1 →
      u = 1 ∨ u = x ∨ u = y ∨ u = x * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu hu2
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hy : orderOf y = 2 := h.y_ord
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hTS : IsSylowOf 2 T (centralizer ({x} : Set G)) := hT.1
  have hxT : x ∈ T := hT.2.1
  have hyc : ∀ t ∈ T, t * y = y * t := hT.2.2.2.1
  have hxy : x * y = y * x := hyc x hxT
  have hL := (Setup30.layer h).1
  have hyL : y ∈ Ly K y := (Setup30.layer h).2.1
  have hLH : Ly K y ≤ pumpUp 2 (Ly K y) y := le_pumpUp h
  set L : Subgroup G := Ly K y with hLdef
  set U : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hU
  set C1 : Subgroup G := CxK x L with hC1
  have hnormL : ∀ g ∈ U, g ∈ normalizer (L : Set G) := fun g hg => by
    rw [← hlayerU]
    exact mem_normalizer_pLayerOf (Subgroup.le_normalizer hg)
  have huU : u ∈ U := ⟨hu.2, hu.1.1⟩
  have hTU : ∀ t ∈ T, t ∈ U := fun t ht =>
    ⟨hTS.le ht, mem_centralizer_singleton_iff.2 (hyc t ht)⟩
  have huC1 : u ∈ C1 := by
    refine ⟨hu.2, hnormL u huU, TwoThin.mem_normalizer_pPrimeCoreOf (hnormL u huU),
      fun l hl => ?_⟩
    obtain ⟨-, ⟨-, -, hc⟩⟩ := hu.1
    have h1 : ⁅l, u⁆ ∈ pPrimeCoreOf 2 (pumpUp 2 L y) := hc l (hLH hl)
    have h2 : ⁅l, u⁆ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hnormL u huU) l⁻¹).mp (Subgroup.inv_mem _ hl)
      rw [commutatorElement_def]
      have e : l * u * l⁻¹ * u⁻¹ = l * (u * l⁻¹ * u⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hl this
    exact inf_pPrimeCoreOf_le hLH (Subgroup.mem_inf.2 ⟨h2, h1⟩)
  have hf : ∀ t ∈ T, ∀ c ∈ C1, t * c * t⁻¹ ∈ C1 := by
    intro t ht c hc
    have hmL := hnormL t (hTU t ht)
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTS.le ht) hc.1)
      (Subgroup.inv_mem _ (hTS.le ht)),
      Obs.conj_mem_centralizerSection hmL (TwoThin.mem_normalizer_pPrimeCoreOf hmL) hc.2⟩
  have hTn : T ≤ normalizer (C1 : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hf t ht c hc, fun hc => ?_⟩
    have := hf t⁻¹ (T.inv_mem ht) _ hc
    have e : t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ = c := by group
    rwa [e] at this
  have hK₁C : T ⊔ C1 ≤ centralizer ({x} : Set G) := sup_le hTS.le inf_le_left
  have hK₁n : T ⊔ C1 ≤ normalizer (C1 : Set G) := sup_le hTn Subgroup.le_normalizer
  have hTK₁ : IsSylowOf 2 T (T ⊔ C1) := hTS.of_le le_sup_left hK₁C
  have hSyl : IsSylowOf 2 (T ⊓ C1) C1 := hTK₁.inf_of_le_normalizer le_sup_right hK₁n
  obtain ⟨R, hR, huR⟩ := S3.exists_isSylowOf_ge (P := zpowers u) (K := C1)
    (Subgroup.zpowers_le.2 huC1) (isPGroup_zpowers_of_involution hu2)
  obtain ⟨k, hkC1, hk⟩ := hSyl.exists_mem_conj hR
  have hw : k⁻¹ * u * k ∈ T ⊓ C1 := (hk u).1 (huR (Subgroup.mem_zpowers u))
  have hw2 : (k⁻¹ * u * k) * (k⁻¹ * u * k) = 1 := by
    calc (k⁻¹ * u * k) * (k⁻¹ * u * k) = k⁻¹ * (u * u) * k := by group
      _ = 1 := by rw [hu2]; group
  have hcases := Setup30.omega_CTL h hT _ hw.1 hw.2.2 hw2
  have hueq : u = k * (k⁻¹ * u * k) * k⁻¹ := by group
  have hkx : k * x = x * k := mem_centralizer_singleton_iff.1 hkC1.1
  have huy : u * y = y * u := mem_centralizer_singleton_iff.1 hu.1.1
  have hky : (k * y * k⁻¹) * y = y * (k * y * k⁻¹) → k * y * k⁻¹ = y := by
    intro hc
    have hcomm : ⁅y, k⁆ ∈ pPrimeCoreOf 2 L := hkC1.2.2.2 y hyL
    have hcomm' : ⁅k, y⁆ ∈ pPrimeCoreOf 2 L := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hcomm
    have hodd : Odd (orderOf ⁅k, y⁆) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) (Subgroup.orderOf_dvd_natCard _ hcomm')
    refine eq_of_mul_odd hy2 hodd ?_ ?_ hc
    · rw [commutatorElement_def]
      group
    · calc (k * y * k⁻¹) * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
        _ = 1 := by rw [hy2]; group
  rcases hcases with e | e | e | e
  · left
    rw [hueq, e]
    group
  · right; left
    rw [hueq, e]
    calc k * x * k⁻¹ = x * k * k⁻¹ := by rw [hkx]
      _ = x := by group
  · right; right; left
    rw [e] at hueq
    rw [hueq]
    exact hky (by rw [← hueq]; exact huy)
  · right; right; right
    rw [e] at hueq
    have h1 : k * (x * y) * k⁻¹ = x * (k * y * k⁻¹) := by
      calc k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
        _ = x * (k * y * k⁻¹) := by
          have : k * x * k⁻¹ = x := by
            calc k * x * k⁻¹ = x * k * k⁻¹ := by rw [hkx]
              _ = x := by group
          rw [this]
    rw [h1] at hueq
    have hu₂ : k * y * k⁻¹ = x * u := by
      rw [hueq, ← mul_assoc, hx2, one_mul]
    have hc : (k * y * k⁻¹) * y = y * (k * y * k⁻¹) := by
      rw [hu₂]
      calc x * u * y = x * (u * y) := by rw [mul_assoc]
        _ = x * (y * u) := by rw [huy]
        _ = (x * y) * u := by rw [mul_assoc]
        _ = (y * x) * u := by rw [hxy]
        _ = y * (x * u) := by rw [mul_assoc]
    rw [hueq, hky hc]

theorem prop305_of_F (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T) :
    pLayerOf 2 (CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G)) = ⊥ ∧
      ∀ u ∈ CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G), u * u = 1 →
        u = 1 ∨ u = x ∨ u = y ∨ u = x * y :=
  ⟨pLayer_C0_eq_bot h (S3Pump304.prop304_of_F h hT hF).2,
    invol_C0 h hT (S3Pump304.prop304_of_F h hT hF).2⟩

end Main

end S3Pump305

end CFSG.GH74.Generic.BProg.B3
