module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Norm
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_10

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

omit [Finite G] in
theorem conj_mem_of_relIndex_two (hS2 : T.relIndex S = 2) (hTS : T ≤ S) {s : G} (hs : s ∈ S)
    {t : G} (ht : t ∈ T) : s * t * s⁻¹ ∈ T := by
  have hidx : (T.subgroupOf S).index = 2 := hS2
  have hN := Subgroup.normal_of_index_eq_two hidx
  exact hN.conj_mem ⟨t, hTS ht⟩ ht ⟨s, hs⟩

theorem eight_le_card_P (h : HBase G x S T P Q Rd F) {V : Subgroup G} (hVP : V ≤ P)
    (hV : IsFour V) (hVn : ¬ ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) : 8 ≤ Nat.card P := by
  have hVneP : V ≠ P := by
    intro e
    apply hVn
    intro t ht v hv
    rw [e] at hv ⊢
    exact h.P_normal.2 t ht v hv
  have hP4' : 4 ≤ Nat.card P := by
    have := Subgroup.card_le_of_le hVP
    rwa [hV.2] at this
  have hpg : IsPGroup 2 ↥P := h.T_pgroup.to_le h.P_le_T
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  by_contra hlt
  have hP4 : Nat.card P = 4 := by
    by_cases hn2 : n ≤ 2
    · interval_cases n
      · rw [pow_zero] at hn; omega
      · rw [pow_one] at hn; omega
      · rw [hn]; norm_num
    · exfalso
      have h8' : (8 : ℕ) ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact hVneP (Subgroup.eq_of_le_of_card_ge hVP (by rw [hP4, hV.2]))

theorem k1_of_facts (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (h127 : After127 G x z S T P Q Rd F) (hf3 : IP_f3 x P) (hzV : IP_z_V z P)
    (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hclosed : IP_P_closed x T P)
    (hdih : IP_Rd_dihedral x Rd) (hfuse : IP_Rd_fuse x P Rd) (hTn : IP_T_normal x z T P Rd) :
    T.relIndex S = 2 → ∀ V : Subgroup G, V ≤ P → IsFour V →
      (¬ ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) → ∀ s ∈ S, s ∉ T →
        s ∉ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
  intro hS2 V hVP hV hVn s hsS hsT hsN
  obtain ⟨f, y, c⟩ := exists_ctx h h127 hf3 hzV hVP hV hsS hsT hsN
  have hsyl := EV_isSylow h h127 hout hcf hclosed hf3 hzV hVP hV hsS hsT hsN
  have hE8 : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 8 := card_E h hVP hV
  have hEab : IsElemAb2 (V ⊔ Subgroup.zpowers x) :=
    isElemAb2_sup_zpowers hV h.x_sq (fun v hv => h.x_central v (h.P_le_T (hVP hv)))
  have hET : V ⊔ Subgroup.zpowers x ≤ T := E_le_T h hVP
  have hEc : T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      V ⊔ Subgroup.zpowers x := by
    have hpg : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) :
        Set G)) := h.T_pgroup.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
    exact sylow2_eq_of_le hsyl hpg (le_inf hET hsyl.1) inf_le_right
  have hzV' : z ∈ V := hzV V hVP hV
  have hz1 : z ≠ 1 := hz.z_ne_one
  have h4 : Nat.card (omegaZ T) = 4 := by
    rcases h127.card_Z with h4 | h8
    · exact h4
    · exfalso
      apply hVn
      intro t ht v hv
      have htZ : t ∈ omegaZ T := by rw [← h127.T_eq_Z h8]; exact ht
      have e : t * v * t⁻¹ = v := by rw [htZ.2.2 v (h.P_le_T (hVP hv))]; group
      rw [e]
      exact hv
  have K : K1Ctx G x z S T P Q Rd F V :=
    ⟨h, hz, h127, h4, hVP, hV, hzV', hEc, eight_le_card_P h hVP hV hVn, hdih, hfuse, hTn⟩
  have hTnorm : ∀ a, a ∈ T ↔ s * a * s⁻¹ ∈ T := by
    intro a
    refine ⟨fun ha => conj_mem_of_relIndex_two hS2 h.T_le_S hsS ha, fun ha => ?_⟩
    have := conj_mem_of_relIndex_two hS2 h.T_le_S (S.inv_mem hsS) ha
    simpa [mul_assoc] using this
  have hszs : s * z * s⁻¹ = z := by
    have h1 : s * z * s⁻¹ ∈ V := c.a_V hzV'
    have h2 : s * z * s⁻¹ ∈ omegaZ T := omegaZ_conj_mem hTnorm (hz.mem_Z h.P_le_T)
    rcases h.P_inf_Z hz h4 (hVP h1) h2 with e | e
    · exact absurd (conj_inj s (e.trans (by group))) hz1
    · exact e
  have hzS : ∀ s' ∈ S, s' * z = z * s' := by
    intro s' hs'
    have key : s' * z * s'⁻¹ = z := by
      by_cases hs'T : s' ∈ T
      · rw [← hz.z_central s' hs'T]; group
      · have ht : s⁻¹ * s' ∈ T := by
          rcases pigeon_of_relIndex_two hS2 hsS hs' with e | e | e
          · exact absurd e hsT
          · exact absurd e hs'T
          · exact e
        have hzt : z * (s⁻¹ * s') = (s⁻¹ * s') * z := hz.z_central _ ht
        calc s' * z * s'⁻¹ = s * ((s⁻¹ * s') * z * (s⁻¹ * s')⁻¹) * s⁻¹ := by group
          _ = s * (z * (s⁻¹ * s') * (s⁻¹ * s')⁻¹) * s⁻¹ := by rw [← hzt]
          _ = s * z * s⁻¹ := by group
          _ = z := hszs
    calc s' * z = (s' * z * s'⁻¹) * s' := by group
      _ = z * s' := by rw [key]
  have hNV : ∀ n ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G),
      ∀ w ∈ V, n * w * n⁻¹ ∈ V := by
    intro n hn w hw
    by_cases hw1 : w = 1
    · rw [hw1]; simp
    · have hE' : n * w * n⁻¹ ∈ V ⊔ Subgroup.zpowers x := Ctx.conjE hn (Ctx.V_le_E hw)
      rw [c.V_iff hE']
      intro hnc
      exact c.nc_V w hw hw1 ((ConjTo.conj_iff n).1 hnc)
  have horb1 : {u | ∃ n ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z}, n * x * n⁻¹ = u}.ncard = 4 := by
    have hset : {u | ∃ n ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {z}, n * x * n⁻¹ = u} = (fun w => x * w) '' (V : Set G) := by
      ext u
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hnE : n * x * n⁻¹ ∈ V ⊔ Subgroup.zpowers x := Ctx.conjE hn.1 Ctx.x_mem_E
        have hnc : ConjTo x (n * x * n⁻¹) := ⟨n, rfl⟩
        rcases c.E_cases hnE with hV' | ⟨w, hw, hw'⟩
        · exact absurd hnc ((c.V_iff hnE).1 hV')
        · exact ⟨w, hw, hw'.symm⟩
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨g, hgN, hgV, hgx⟩ := c.words w hw
        refine ⟨g, ⟨hgN, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hgx⟩
        have hgz := hgV z hzV'
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [hgz]
    rw [hset, Set.ncard_image_of_injective _ (mul_right_injective x)]
    have e : Nat.card (V : Set G) = Nat.card V := rfl
    rw [← Nat.card_coe_set_eq, e]
    exact hV.2
  have h4M := ncard_conj_mul_card_inf_centralizer
    (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z}) x
  rw [horb1] at h4M
  have hElt : V ⊔ Subgroup.zpowers x < T := by
    refine lt_of_le_of_ne hET (fun e => hVn (fun t ht w hw => ?_))
    have hEn : NormalIn (V ⊔ Subgroup.zpowers x) T := ⟨hET, fun t' ht' u hu => by
      rw [e] at hu ⊢
      exact T.mul_mem (T.mul_mem ht' hu) (T.inv_mem ht')⟩
    exact V_normal h hEn hVP ht hw
  obtain ⟨t, htT, htE, htn⟩ := exists_mem_normalizer_of_lt h.T_pgroup hElt
  have htN : t ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff.2 htn
  have hc4 : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV.2
  obtain ⟨v, hvV, hv⟩ : ∃ v ∈ (V : Set G), v ∉ ({1, z} : Set G) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (by rw [Set.ncard_pair hz1.symm, hc4]; norm_num)
      (Set.toFinite _)
  have hv1 : v ≠ 1 := fun e => hv (Or.inl e)
  have hvz : v ≠ z := fun e => hv (Or.inr e)
  have hVeq : V = Subgroup.zpowers z ⊔ Subgroup.zpowers v :=
    isFour_eq_pair hV hzV' hvV hz1 hv1 hvz.symm
  have htz : t * z * t⁻¹ = z := by rw [← hz.z_central t htT]; group
  have htv : t * v * t⁻¹ = z * v := by
    rcases isFour_mem_cases hV hzV' hvV hz1 hv1 hvz.symm (hNV t htN v hvV) with e | e | e | e
    · exact absurd (conj_inj t (e.trans (by group))) hv1
    · exact absurd (conj_inj t (e.trans htz.symm)) hvz
    · exfalso
      apply htE
      have hvt : v * t = t * v := by
        calc v * t = (t * v * t⁻¹) * t := by rw [e]
          _ = t * v := by group
      have htc : t ∈ T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
        refine ⟨htT, Subgroup.mem_centralizer_iff.2 (fun u hu => ?_)⟩
        have hle : V ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({t} : Set G) := by
          rw [hVeq]
          refine sup_le (sup_le ?_ ?_) ?_
          · exact (Subgroup.zpowers_le).2
              (Subgroup.mem_centralizer_singleton_iff.2 (hz.z_central t htT))
          · exact (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hvt)
          · exact (Subgroup.zpowers_le).2
              (Subgroup.mem_centralizer_singleton_iff.2 (h.x_central t htT))
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
      rw [hEc] at htc
      exact htc
    · exact e
  have htM : t ∈ (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z}) ⊓ Subgroup.centralizer {x} :=
    ⟨⟨htN, Subgroup.mem_centralizer_singleton_iff.2 (hz.z_central t htT).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (h.x_central t htT).symm⟩
  have horb2 : {u | ∃ n ∈ (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z}) ⊓ Subgroup.centralizer {x}, n * v * n⁻¹ = u}.ncard = 2 := by
    apply le_antisymm
    · have hsub : {u | ∃ n ∈ (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) :
          Set G) ⊓ Subgroup.centralizer {z}) ⊓ Subgroup.centralizer {x}, n * v * n⁻¹ = u} ⊆
          (V : Set G) \ {1, z} := by
        rintro u ⟨n, hn, rfl⟩
        refine ⟨hNV n hn.1.1 v hvV, ?_⟩
        have hnz : n * z * n⁻¹ = z := by
          rw [Subgroup.mem_centralizer_singleton_iff.1 hn.1.2]; group
        rintro (e | e)
        · exact hv1 (conj_inj n (e.trans (by group)))
        · exact hvz (conj_inj n (e.trans hnz.symm))
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_sdiff_pair_le hV.2.le hzV' hz1)
    · have hsub : ({v, z * v} : Set G) ⊆ {u | ∃ n ∈ (Subgroup.normalizer
          ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓ Subgroup.centralizer {z}) ⊓
          Subgroup.centralizer {x}, n * v * n⁻¹ = u} := by
        rintro u (rfl | rfl)
        · exact ⟨1, Subgroup.one_mem _, by group⟩
        · exact ⟨t, htM, htv⟩
      have hne : v ≠ z * v := by
        intro e
        apply hz1
        calc z = z * v * v⁻¹ := by group
          _ = v * v⁻¹ := by rw [← e]
          _ = 1 := by group
      calc 2 = ({v, z * v} : Set G).ncard := (Set.ncard_pair hne).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2M := ncard_conj_mul_card_inf_centralizer
    ((Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z}) ⊓ Subgroup.centralizer {x}) v
  rw [horb2] at h2M
  have hE_le : V ⊔ Subgroup.zpowers x ≤
      ((Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {z}) ⊓ Subgroup.centralizer {x}) ⊓ Subgroup.centralizer {v} := by
    intro e he
    have hc : ∀ u ∈ V ⊔ Subgroup.zpowers x, e ∈ Subgroup.centralizer {u} :=
      fun u hu => Subgroup.mem_centralizer_singleton_iff.2 ((hEab e he).2 u hu)
    exact ⟨⟨⟨Subgroup.le_normalizer he, hc z (Subgroup.mem_sup_left hzV')⟩, hc x Ctx.x_mem_E⟩,
      hc v (Subgroup.mem_sup_left hvV)⟩
  have h8 := Subgroup.card_dvd_of_le hE_le
  rw [hE8] at h8
  have h64 : 64 ∣ Nat.card (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
      Subgroup.centralizer {z} : Subgroup G) := by
    obtain ⟨k, hk⟩ := h8
    exact ⟨k, by rw [← h4M, ← h2M, hk]; ring⟩
  have hEpg : IsPGroup 2 ↥(V ⊔ Subgroup.zpowers x) := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  obtain ⟨R, hR, hER⟩ := exists_sylow2_ge hEpg (hE_le.trans (inf_le_left.trans inf_le_left))
  have hR64 : 64 ≤ Nat.card R := by
    have h5 : R.relIndex (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓
        Subgroup.centralizer {z}) * Nat.card R = Nat.card (Subgroup.normalizer
          ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓ Subgroup.centralizer {z} :
            Subgroup G) := by
      have := Subgroup.relIndex_mul_card (H := R) (K := Subgroup.normalizer
        ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓ Subgroup.centralizer {z})
      rwa [inf_of_le_left hR.1] at this
    have hcop : Nat.Coprime 64 (R.relIndex (Subgroup.normalizer
        ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) ⊓ Subgroup.centralizer {z})) := by
      have e64 : (64 : ℕ) = 2 ^ 6 := by norm_num
      rw [e64]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hR.2.2)
    have h6 : 64 ∣ R.relIndex (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) :
        Set G) ⊓ Subgroup.centralizer {z}) * Nat.card R := by
      rw [h5]
      exact h64
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left h6)
  have hSC : IsSylow2In S (Subgroup.centralizer {z}) := by
    have hSle : S ≤ Subgroup.centralizer {z} :=
      fun s' hs' => Subgroup.mem_centralizer_singleton_iff.2 (hzS s' hs')
    refine ⟨hSle, h.S_pgroup, fun hdvd => h.S_sylow.2.2 ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S (Subgroup.centralizer {z}) ⊤ hSle le_top]
    exact dvd_mul_of_dvd_left hdvd _
  obtain ⟨R', hR', hRR'⟩ := exists_sylow2_ge hR.2.1 (hR.1.trans inf_le_right)
  obtain ⟨g, hgC, hg⟩ := sylow2_exists_conj hSC hR'
  have hgz : g⁻¹ * z * g = z := by
    have hgz' : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hgC
    calc g⁻¹ * z * g = g⁻¹ * (g * z) := by rw [hgz']; group
      _ = z := by group
  have hmemS : ∀ a, g⁻¹ * a * g⁻¹⁻¹ ∈ R → a ∈ S := by
    intro a ha
    have h1 : g⁻¹ * a * g⁻¹⁻¹ ∈ R' := hRR' ha
    rw [hg, mem_Hconj] at h1
    simpa [mul_assoc] using h1
  have hE'S : Hconj g⁻¹ (V ⊔ Subgroup.zpowers x) ≤ S := fun a ha => hmemS a (hER ha)
  have hE'8 : Nat.card (Hconj g⁻¹ (V ⊔ Subgroup.zpowers x)) = 8 := by rw [Hconj_card, hE8]
  have hzE' : z ∈ Hconj g⁻¹ (V ⊔ Subgroup.zpowers x) := by
    rw [mem_Hconj, inv_inv, hgz]
    exact Subgroup.mem_sup_left hzV'
  have hNle : Hconj g⁻¹ R ≤
      S ⊓ Subgroup.normalizer ((Hconj g⁻¹ (V ⊔ Subgroup.zpowers x) : Subgroup G) : Set G) := by
    intro a ha
    have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ R := ha
    refine ⟨hmemS a ha', Hconj_normalizer_le g⁻¹ _ ?_⟩
    rw [mem_Hconj]
    exact (hR.1 ha').1
  have hge : 64 ≤ Nat.card (S ⊓ Subgroup.normalizer
      ((Hconj g⁻¹ (V ⊔ Subgroup.zpowers x) : Subgroup G) : Set G) : Subgroup G) :=
    calc 64 ≤ Nat.card R := hR64
      _ = Nat.card (Hconj g⁻¹ R) := (Hconj_card _ _).symm
      _ ≤ _ := Subgroup.card_le_of_le hNle
  have hlt := K.card_normalizer_lt hS2 hE'S (hEab.hconj g⁻¹) hE'8 hzE'
  omega

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
