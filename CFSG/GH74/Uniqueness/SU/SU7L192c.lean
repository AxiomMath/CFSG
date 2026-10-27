module

public import CFSG.GH74.Uniqueness.SU.SU7L192
public import CFSG.GH74.Uniqueness.SU.SU7Gen5
public import CFSG.GH74.Uniqueness.SU.SU7Gen6
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG

namespace Gen

theorem inv_conj_mem {G : Type*} [Group G] {K : Subgroup G} [Finite K] {n : G}
    (hn : ∀ s ∈ K, n * s * n⁻¹ ∈ K) : ∀ s ∈ K, n⁻¹ * s * n ∈ K := by
  have hnN : n ∈ normalizer (K : Set G) := Gen.mem_normalizer_of_conj_le hn
  intro s hs
  have := (mem_normalizer_iff.1 ((normalizer (K : Set G)).inv_mem hnN) s).1 hs
  simpa using this

end Gen

namespace Bar

variable {G : Type} [Group G] {M : Subgroup G}

theorem mk_mem_normalizer {T : Subgroup G} {n : G} (hnM : n ∈ M)
    (hn : n ∈ normalizer (T : Set G)) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hnM⟩ ∈
      normalizer ((barImage M T : Subgroup (Mbar M)) : Set (Mbar M)) := by
  have h1 : (⟨n, hnM⟩ : ↥M) ∈ normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [mem_normalizer_iff]
    intro y
    show (y : G) ∈ T ↔ n * (y : G) * n⁻¹ ∈ T
    exact mem_normalizer_iff.1 hn (y : G)
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (pPrimeCore 2 ↥M))
    (Subgroup.mem_map_of_mem _ h1)

end Bar

namespace L192

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem conj_U (hc : Ctx19 S U M V x z A B R) {n : G}
    (hn : ∀ s ∈ (S : Subgroup G), n * s * n⁻¹ ∈ (S : Subgroup G)) :
    ∀ u ∈ U, n * u * n⁻¹ ∈ U := by
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hmemZ := Base.mem_Zc_iff hc.hyp hc.conf hc.concl
  have hn' := Gen.inv_conj_mem hn
  set N' : Subgroup G := U.map (MulAut.conj n).toMonoidHom with hN'
  have hN'S : N' ≤ (S : Subgroup G) := by
    rintro _ ⟨u, hu, rfl⟩
    exact hn u (Base.U_le_S hc.hyp hu)
  have hN'n : ∀ s ∈ (S : Subgroup G), ∀ y ∈ N', s * y * s⁻¹ ∈ N' := by
    rintro s hs _ ⟨u, hu, rfl⟩
    refine ⟨(n⁻¹ * s * n) * u * (n⁻¹ * s * n)⁻¹, Base.U_norm hc.hyp _ (hn' s hs) u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hN'E : IsE 2 N' := (isE_map (MulAut.conj n).injective).2 (Base.U_isE hc.hyp)
  intro u hu
  have hmem : n * u * n⁻¹ ∈ N' := ⟨u, hu, by simp [MulAut.conj_apply]⟩
  rw [hJ.U_unique N' hN'S hN'n hN'E] at hmem
  exact (hmemZ _).1 hmem

theorem mem_normalizer_T (hc : Ctx19 S U M V x z A B R) {n : G}
    (hn : ∀ s ∈ (S : Subgroup G), n * s * n⁻¹ ∈ (S : Subgroup G)) :
    n ∈ normalizer ((Tsub S U : Subgroup G) : Set G) := by
  have hU1 := conj_U hc hn
  have hU2 : ∀ u ∈ U, n⁻¹ * u * n ∈ U := fun u hu => by
    simpa using conj_U hc (n := n⁻¹) (fun s hs => by simpa using Gen.inv_conj_mem hn s hs) u hu
  apply Gen.mem_normalizer_of_conj_le
  intro t ht
  have ht' : t ∈ centralizer (U : Set G) ⊓ (S : Subgroup G) := ht
  obtain ⟨htc, htS⟩ := Subgroup.mem_inf.1 ht'
  show n * t * n⁻¹ ∈ centralizer (U : Set G) ⊓ (S : Subgroup G)
  refine Subgroup.mem_inf.2 ⟨?_, hn t htS⟩
  rw [mem_centralizer_iff]
  intro u hu
  have hu' := hU2 u hu
  have htcu := mem_centralizer_iff.1 htc (n⁻¹ * u * n) hu'
  calc u * (n * t * n⁻¹) = n * ((n⁻¹ * u * n) * t) * n⁻¹ := by group
    _ = n * (t * (n⁻¹ * u * n)) * n⁻¹ := by rw [htcu]
    _ = (n * t * n⁻¹) * u := by group

theorem normalizer_T_le_M (hc : Ctx19 S U M V x z A B R) {n : G}
    (hn : n ∈ normalizer ((Tsub S U : Subgroup G) : Set G)) : n ∈ M := by
  have hmemZ := Base.mem_Zc_iff hc.hyp hc.conf hc.concl
  have hnU : n ∈ normalizer (U : Set G) := Gen.mem_normalizer_of_conj_le (fun p hp =>
    (hmemZ _).1 (Base.mem_Zc_of_normalizer hn ((hmemZ p).2 hp)))
  have hA := hc.c19.isE16_A
  exact Claim.normalizer_le_M_of_isE hc.hyp (E := U) (F := A) (n := 2) (m := 4)
    (Base.U_le_S hc.hyp) (Base.U_isE hc.hyp) (by norm_num)
    (fun a ha => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hc.c19.A_le ha)).1, Base.T_le_S
      (hc.c19.A_le ha)⟩)
    ⟨hA.1, by rw [hA.2]; norm_num⟩ (by norm_num) hnU

theorem centralizes_U (hc : Ctx19 S U M V x z A B R) {b : G}
    (hb : ∀ s ∈ (S : Subgroup G), b * s * b⁻¹ ∈ (S : Subgroup G)) (hbz : b * z = z * b)
    (hbodd : Odd (orderOf b)) : ∀ u ∈ U, b * u = u * b := by
  have hU' := conj_U hc hb
  have hz2 := Base.z_mul_self hc.conf
  obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := RF.exists_u₀ hc
  have hall := RF.U_cases hc hu₀U hu₀1 hu₀z
  have hbzb : b * z * b⁻¹ = z := by rw [hbz]; group
  have hbu₀ : b * u₀ = u₀ * b := by
    have hm : b * u₀ * b⁻¹ ∈ U := hU' u₀ hu₀U
    rcases hall _ hm with h | h | h | h
    · exfalso
      apply hu₀1
      have : u₀ = b⁻¹ * (b * u₀ * b⁻¹) * b := by group
      rw [this, h]; group
    · exfalso
      apply hu₀z
      have : u₀ = b⁻¹ * (b * u₀ * b⁻¹) * b := by group
      rw [this, h]
      calc b⁻¹ * z * b = b⁻¹ * (z * b) := by group
        _ = b⁻¹ * (b * z) := by rw [hbz]
        _ = z := by group
    · calc b * u₀ = (b * u₀ * b⁻¹) * b := by group
        _ = u₀ * b := by rw [h]
    · exfalso
      have h2 : b * b * u₀ = u₀ * (b * b) := by
        calc b * b * u₀ = (b * (b * u₀ * b⁻¹) * b⁻¹) * (b * b) := by group
          _ = (b * (z * u₀) * b⁻¹) * (b * b) := by rw [h]
          _ = ((b * z * b⁻¹) * (b * u₀ * b⁻¹)) * (b * b) := by group
          _ = (z * (z * u₀)) * (b * b) := by rw [hbzb, h]
          _ = u₀ * (b * b) := by
            have hzz : z * (z * u₀) = u₀ := by rw [← mul_assoc, hz2, one_mul]
            rw [hzz]
      have h3 : Commute (b ^ 2) u₀ := by
        show b ^ 2 * u₀ = u₀ * b ^ 2
        rw [pow_two]; exact h2
      have h4 := (Gen.commute_of_pow h3 (Nat.coprime_two_left.2 hbodd)).eq
      apply Base.z_ne_one hc.conf
      have h5 : z * u₀ = u₀ := by
        calc z * u₀ = b * u₀ * b⁻¹ := h.symm
          _ = (u₀ * b) * b⁻¹ := by rw [h4]
          _ = u₀ := by group
      have : z * u₀ = 1 * u₀ := by rw [h5, one_mul]
      exact mul_right_cancel this
  intro u hu
  rcases hall u hu with rfl | rfl | rfl | rfl
  · simp
  · exact hbz
  · exact hbu₀
  · calc b * (z * u₀) = (b * z) * u₀ := by group
      _ = (z * b) * u₀ := by rw [hbz]
      _ = z * (b * u₀) := by group
      _ = z * (u₀ * b) := by rw [hbu₀]
      _ = z * u₀ * b := by group

theorem exists_three_elt (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∃ b : G, (∀ s ∈ (S : Subgroup G), b * s * b⁻¹ ∈ (S : Subgroup G)) ∧ b * z = z * b ∧
      Odd (orderOf b) ∧ (∃ y ∈ Tsub S U, b * y * b⁻¹ ≠ y) ∧
      ∀ s ∈ (S : Subgroup G), s ∉ R → s⁻¹ * (b * s * b⁻¹) ∉ R := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  obtain ⟨ψ, hψ, hker, -⟩ := exists_surj_alt5_G hKI3 hKI4 hc
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  obtain ⟨hR32, hzR, hsq⟩ := RF.R_facts hc
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
  set S₀ : Subgroup ↥C := (S : Subgroup G).subgroupOf C with hS₀
  set R₀ : Subgroup ↥C := R.subgroupOf C with hR₀
  have hS₀p : IsPGroup 2 ↥S₀ := Bar.isPGroup_subgroupOf S.isPGroup' C
  have hRS : R₀ ≤ S₀ := fun r hr => hc.c19.R_le hr
  have hS128 : Nat.card S₀ = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]; exact hJ.card_S
  have hR32' : Nat.card R₀ = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv]; exact hR32
  have hOk : pPrimeCore 2 ↥C ≤ ψ.ker := by rw [hker]; exact le_sup_right
  have hkS : ψ.ker ≤ S₀ ⊔ pPrimeCore 2 ↥C := by rw [hker]; exact sup_le_sup_right hRS _
  have hkerS : S₀ ⊓ ψ.ker = R₀ := by
    apply le_antisymm
    · rintro s ⟨hsS, hsK⟩
      rw [hker] at hsK
      obtain ⟨r, hr, o, ho, hro⟩ := Subgroup.mem_sup_of_normal_right.1 hsK
      have hoS : o ∈ S₀ := by
        have : o = r⁻¹ * s := by rw [← hro]; group
        rw [this]; exact S₀.mul_mem (S₀.inv_mem (hRS hr)) hsS
      have h1 : o ∈ S₀ ⊓ pPrimeCore 2 ↥C := ⟨hoS, ho⟩
      rw [Gen.inf_eq_bot_of_isPGroup hS₀p hOodd, Subgroup.mem_bot] at h1
      rw [← hro, h1, mul_one]; exact hr
    · exact le_inf hRS (by rw [hker]; exact le_sup_left)
  have hP4 : Nat.card (S₀.map ψ) = 4 := by
    have h := Gen.card_map_mul_card_inf_ker ψ S₀
    rw [hkerS, hS128, hR32'] at h
    omega
  have hPe : ∀ g ∈ S₀.map ψ, g * g = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul]
    have hk : s * s ∈ ψ.ker := by
      rw [hker]; exact Subgroup.mem_sup_left (RF.sq_mem_R hc hs)
    exact hk
  obtain ⟨c, hc1, hc3, hcP, hcfpf⟩ := Gen.alt5_exists_three_fpf hP4 hPe
  obtain ⟨c₀, hc₀⟩ := hψ c
  have hc₀P : ∀ s ∈ S₀, ψ (c₀ * s * c₀⁻¹) ∈ S₀.map ψ := fun s hs => by
    rw [map_mul, map_mul, map_inv, hc₀]; exact hcP _ ⟨s, hs, rfl⟩
  obtain ⟨n, hnS, hnψ⟩ := Gen.exists_norm_lift hOodd hS₀p ψ hOk hkS c₀ hc₀P
  have hψn : ψ n = c := by rw [hnψ, hc₀]
  have hn3 : ψ n * ψ n * ψ n = 1 := by rw [hψn]; exact hc3
  obtain ⟨j, hjodd, hjψ⟩ := Gen.exists_odd_pow ψ hn3
  have hnN : n ∈ normalizer (S₀ : Set ↥C) := Gen.mem_normalizer_of_conj_le hnS
  have hbS : ∀ s ∈ S₀, n ^ j * s * (n ^ j)⁻¹ ∈ S₀ := fun s hs =>
    (mem_normalizer_iff.1 ((normalizer (S₀ : Set ↥C)).pow_mem hnN j) s).1 hs
  have hbfpf : ∀ p ∈ S₀.map ψ, p ≠ 1 → ψ (n ^ j) * p * (ψ (n ^ j))⁻¹ ≠ p := by
    intro p hp hp1 h
    apply hcfpf p hp hp1
    rcases hjψ with h' | h'
    · rw [h', hψn] at h; exact h
    · rw [h', hψn, inv_inv] at h
      have h2 : p * c = c * p := by
        calc p * c = c * (c⁻¹ * p * c) := by group
          _ = c * p := by rw [h]
      calc c * p * c⁻¹ = p * c * c⁻¹ := by rw [← h2]
        _ = p := by group
  refine ⟨((n ^ j : ↥C) : G), ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hbS ⟨s, hSC hs⟩ hs
  · exact RF.cent_comm (n ^ j : ↥C).2
  · rw [Subgroup.orderOf_coe]; exact hjodd
  · by_contra hcon
    push Not at hcon
    have hTR : Tsub S U ≤ R := by
      intro y hy
      have hyS : y ∈ (S : Subgroup G) := Base.T_le_S hy
      have hyC : y ∈ C := hSC hyS
      have h1 : n ^ j * (⟨y, hyC⟩ : ↥C) * (n ^ j)⁻¹ = ⟨y, hyC⟩ := Subtype.ext (hcon y hy)
      have h2 : ψ (n ^ j) * ψ ⟨y, hyC⟩ * (ψ (n ^ j))⁻¹ = ψ ⟨y, hyC⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul, h1]
      have hyP : ψ ⟨y, hyC⟩ ∈ S₀.map ψ := ⟨⟨y, hyC⟩, hyS, rfl⟩
      have h3 : ψ ⟨y, hyC⟩ = 1 := by
        by_contra h4; exact hbfpf _ hyP h4 h2
      have h4 : (⟨y, hyC⟩ : ↥C) ∈ S₀ ⊓ ψ.ker := ⟨hyS, h3⟩
      rw [hkerS] at h4
      exact h4
    have := Subgroup.card_le_of_le hTR
    rw [hJ.card_T, hR32] at this
    omega
  · intro s hsS hsR hmem
    have hsC : s ∈ C := hSC hsS
    have hσS : (⟨s, hsC⟩ : ↥C) ∈ S₀ := hsS
    have hs1 : ψ ⟨s, hsC⟩ ≠ 1 := by
      intro h1
      apply hsR
      have h4 : (⟨s, hsC⟩ : ↥C) ∈ S₀ ⊓ ψ.ker := ⟨hσS, h1⟩
      rw [hkerS] at h4
      exact h4
    have hker1 : (⟨s, hsC⟩ : ↥C)⁻¹ * (n ^ j * ⟨s, hsC⟩ * (n ^ j)⁻¹) ∈ ψ.ker := by
      rw [hker]
      exact Subgroup.mem_sup_left hmem
    simp only [MonoidHom.mem_ker, map_mul, map_inv] at hker1
    apply hbfpf _ ⟨⟨s, hsC⟩, hσS, rfl⟩ hs1
    calc ψ (n ^ j) * ψ ⟨s, hsC⟩ * (ψ (n ^ j))⁻¹
        = ψ ⟨s, hsC⟩ * ((ψ ⟨s, hsC⟩)⁻¹ * (ψ (n ^ j) * ψ ⟨s, hsC⟩ * (ψ (n ^ j))⁻¹)) := by group
      _ = ψ ⟨s, hsC⟩ := by rw [hker1, mul_one]

theorem lemma192_c (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∃ _ : ((Tsub S U ⊔ centralizer ((Tsub S U : Subgroup G) : Set G)).subgroupOf
        (normalizer ((Tsub S U : Subgroup G) : Set G))).Normal,
      Nonempty (↥(normalizer ((Tsub S U : Subgroup G) : Set G)) ⧸
        ((Tsub S U ⊔ centralizer ((Tsub S U : Subgroup G) : Set G)).subgroupOf
          (normalizer ((Tsub S U : Subgroup G) : Set G))) ≃*
        Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)) := by
  classical
  have hH := hc.hyp
  have hconf := hc.conf
  have hcl := hc.concl
  obtain ⟨Hh, H₀, hN, hdisj, hH₀Hh, ⟨e₀⟩, hHh, hH₀C, hcomm, -, hcard⟩ := hcl.normalizerT
  set T : Subgroup G := Tsub S U with hTdef
  set N : Subgroup G := normalizer (T : Set G) with hNdef
  set D : Subgroup G := T ⊔ centralizer (T : Set G) with hDdef
  have hTS : T ≤ (S : Subgroup G) := Base.T_le_S
  have hTM : T ≤ M := hTS.trans hconf.S_le
  have hTp : IsPGroup 2 ↥T := S.isPGroup'.to_le hTS
  have hNM : N ≤ M := fun n hn => normalizer_T_le_M hc hn
  have hUT : U ≤ T := Base.U_le_T hH hconf hcl
  have hmemZ := Base.mem_Zc_iff hH hconf hcl
  obtain ⟨b, hbS, hbz, hbodd, ⟨y₀, hy₀T, hby₀⟩, -⟩ := exists_three_elt hKI3 hKI4 hc
  have hbN : b ∈ N := mem_normalizer_T hc hbS
  have hbM : b ∈ M := hNM hbN
  have hbU := centralizes_U hc hbS hbz hbodd
  have hTbp : IsPGroup 2 ↥(barImage M T) := (Bar.isPGroup_subgroupOf hTp M).map _
  have hHn : ∀ h ∈ Hh, ∀ t ∈ barImage M T, h * t * h⁻¹ ∈ barImage M T := by
    intro h hh t ht
    have : h ∈ normalizer ((barImage M T : Subgroup (Mbar M)) : Set (Mbar M)) := by
      rw [hN]; exact Subgroup.mem_sup_right hh
    exact (mem_normalizer_iff.1 this t).1 ht
  have hUb : ∀ u ∈ barImage M U, ∀ t ∈ barImage M T, u * t = t * u := by
    intro u hu t ht
    obtain ⟨u', hu', rfl⟩ := Claim.mem_barImage_iff.1 hu
    obtain ⟨t', ht', rfl⟩ := Claim.mem_barImage_iff.1 ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_Zc.1 ((hmemZ _).2 hu')).2 t' ht')
  have hbb : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩ ∈ barImage M T ⊔ Hh := by
    rw [← hN]; exact Bar.mk_mem_normalizer hbM hbN
  have hbbodd : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩)) := by
    refine Odd.of_dvd_nat (n := orderOf b) hbodd ?_
    have := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (⟨b, hbM⟩ : ↥M)
    rwa [Subgroup.orderOf_mk] at this
  have hbbU : ∀ u ∈ barImage M U,
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩ * u =
        u * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩ := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := Claim.mem_barImage_iff.1 hu
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbU _ hu')
  have hbbT : ∃ y ∈ barImage M T,
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩ * y *
        (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨b, hbM⟩)⁻¹ ≠ y := by
    have hy₀M : y₀ ∈ M := hTM hy₀T
    refine ⟨QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y₀, hy₀M⟩,
      Claim.mem_barImage_iff.2 ⟨⟨y₀, hy₀M⟩, hy₀T, rfl⟩, fun h => hby₀ ?_⟩
    have hbyT : b * y₀ * b⁻¹ ∈ T := (mem_normalizer_iff.1 hbN y₀).1 hy₀T
    have hbyM : b * y₀ * b⁻¹ ∈ M := hTM hbyT
    refine Bar.eq_of_proj_eq hTp hTM hbyT hy₀T ?_
    rw [← h, ← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨hc3, hcent⟩ := Gen.cent_le_of_three_elt hTbp hHn (Claim.barImage_mono hUT) hUb hcard
    hbb hbbodd hbbU hbbT
  obtain ⟨ν, hνs, hνk⟩ := Gen.exists_hom_complement hHn hdisj
  let πN : ↥N →* Mbar M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hNM)
  have hmem : ∀ n : ↥N, πN n ∈ barImage M T ⊔ Hh := fun n => by
    rw [← hN]; exact Bar.mk_mem_normalizer (hNM n.2) n.2
  let Φ : ↥N →* ↥Hh := ν.comp (πN.codRestrict (barImage M T ⊔ Hh) hmem)
  have hΦ : ∀ n : ↥N, Φ n = 1 ↔ πN n ∈ barImage M T := fun n => hνk _
  have hΦs : Function.Surjective Φ := by
    intro h
    obtain ⟨p, hp⟩ := hνs h
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (p : Mbar M)
    have hgN : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ ∈
        normalizer ((barImage M T : Subgroup (Mbar M)) : Set (Mbar M)) := by
      rw [hN]
      have : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ = (p : Mbar M) := hg
      rw [this]
      exact p.2
    obtain ⟨n, hnM, hnN, hnπ⟩ := Bar.normalizer_lift hTp hTM g.2 hgN
    refine ⟨⟨n, hnN⟩, ?_⟩
    have hcod : (πN.codRestrict (barImage M T ⊔ Hh) hmem) ⟨n, hnN⟩ = p := by
      apply Subtype.ext
      show QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hNM hnN⟩ = (p : Mbar M)
      rw [hnπ]; exact hg
    show ν ((πN.codRestrict (barImage M T ⊔ Hh) hmem) ⟨n, hnN⟩) = h
    rw [hcod]; exact hp
  have hΦker : Φ.ker = D.subgroupOf N := by
    ext ⟨n, hnN⟩
    rw [MonoidHom.mem_ker, hΦ, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      obtain ⟨t, ht, hπt⟩ := Claim.mem_barImage_iff.1 hn
      have htM : (t : G) ∈ M := t.2
      have hnM : n ∈ M := hNM hnN
      have hoM : (t : G)⁻¹ * n ∈ M := M.mul_mem (M.inv_mem htM) hnM
      have hoO : (⟨(t : G)⁻¹ * n, hoM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
        have h0 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨(t : G)⁻¹ * n, hoM⟩ : ↥M) = 1 := by
          have : (⟨(t : G)⁻¹ * n, hoM⟩ : ↥M) = t⁻¹ * ⟨n, hnM⟩ := Subtype.ext (by simp)
          rw [this, map_mul, map_inv]
          have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) t =
              QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hnM⟩ := hπt
          rw [h1]
          exact inv_mul_cancel _
        exact (QuotientGroup.eq_one_iff _).1 h0
      have hoN : (t : G)⁻¹ * n ∈ N :=
        N.mul_mem (N.inv_mem (Subgroup.le_normalizer ht)) hnN
      have hoC : (t : G)⁻¹ * n ∈ centralizer (T : Set G) := by
        rw [mem_centralizer_iff]
        intro t' ht'
        set o : G := (t : G)⁻¹ * n with ho
        have h1 : o * t' * o⁻¹ ∈ T := (mem_normalizer_iff.1 hoN t').1 ht'
        have hcomm' : o * t' * o⁻¹ * t'⁻¹ ∈ T :=
          T.mul_mem h1 (T.inv_mem ht')
        have hmem2 : (⟨o, hoM⟩ : ↥M) * ⟨t', hTM ht'⟩ * ⟨o, hoM⟩⁻¹ * ⟨t', hTM ht'⟩⁻¹ ∈
            pPrimeCore 2 ↥M := by
          have hn1 := (inferInstance : (pPrimeCore 2 ↥M).Normal).conj_mem _ ((pPrimeCore 2 ↥M).inv_mem hoO)
            ⟨t', hTM ht'⟩
          have : (⟨o, hoM⟩ : ↥M) * ⟨t', hTM ht'⟩ * ⟨o, hoM⟩⁻¹ * ⟨t', hTM ht'⟩⁻¹ =
              ⟨o, hoM⟩ * (⟨t', hTM ht'⟩ * ⟨o, hoM⟩⁻¹ * ⟨t', hTM ht'⟩⁻¹) := by group
          rw [this]
          exact (pPrimeCore 2 ↥M).mul_mem hoO hn1
        have hmem3 : (⟨o, hoM⟩ : ↥M) * ⟨t', hTM ht'⟩ * ⟨o, hoM⟩⁻¹ * ⟨t', hTM ht'⟩⁻¹ ∈
            T.subgroupOf M := hcomm'
        have hmem4 : (⟨o, hoM⟩ : ↥M) * ⟨t', hTM ht'⟩ * ⟨o, hoM⟩⁻¹ * ⟨t', hTM ht'⟩⁻¹ ∈
            T.subgroupOf M ⊓ pPrimeCore 2 ↥M := ⟨hmem3, hmem2⟩
        rw [Gen.inf_eq_bot_of_isPGroup (Bar.isPGroup_subgroupOf hTp M) (Bar.odd_pPrimeCore M),
          Subgroup.mem_bot] at hmem4
        have h5 := congrArg Subtype.val hmem4
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h5
        calc t' * o = (o * t' * o⁻¹ * t'⁻¹) * (t' * o) := by rw [h5]; group
          _ = o * t' := by group
      have hnn : n = (t : G) * ((t : G)⁻¹ * n) := by group
      show n ∈ D
      rw [hnn]
      exact Subgroup.mul_mem_sup ht hoC
    · intro hnD
      obtain ⟨t, ht, c, hcC, hn⟩ := SU5.mem_sup_of_commute (fun a ha b hb =>
        mem_centralizer_iff.1 hb a ha) hnD
      have hcN : c ∈ N := Gen.mem_normalizer_of_conj_le (fun y hy => by
        have h1 : y * c = c * y := mem_centralizer_iff.1 hcC y hy
        have : c * y * c⁻¹ = y := by
          calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [h1]
            _ = y := by group
        rw [this]; exact hy)
      have hcM : c ∈ M := hNM hcN
      have htM : t ∈ M := hTM ht
      have hcb : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ ∈ barImage M T ⊔ Hh := by
        rw [← hN]; exact Bar.mk_mem_normalizer hcM hcN
      have hcc : ∀ y ∈ barImage M T, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ * y =
          y * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ := by
        intro y hy
        obtain ⟨t', ht', rfl⟩ := Claim.mem_barImage_iff.1 hy
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_iff.1 hcC t' ht').symm
      have hcT := hcent _ hcb hcc
      have hπn : πN ⟨n, hnN⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ *
          QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨c, hcM⟩ := by
        rw [← map_mul]
        show QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hNM hnN⟩ = _
        congr 1
        exact Subtype.ext hn.symm
      rw [hπn]
      exact (barImage M T).mul_mem (Claim.mem_barImage_iff.2 ⟨⟨t, htM⟩, ht, rfl⟩) hcT
  have hnormal : (D.subgroupOf N).Normal := by
    rw [← hΦker]; exact Φ.normal_ker
  refine ⟨hnormal, ?_⟩
  have e1 : ↥N ⧸ D.subgroupOf N ≃* ↥Hh :=
    (QuotientGroup.quotientMulEquivOfEq hΦker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs)
  obtain ⟨e2⟩ := Gen.nonempty_mulEquiv_prod hcomm hH₀C
  have e2' : ↥Hh ≃* ↥(H₀ ⊔ (centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh)) :=
    MulEquiv.subgroupCongr hHh
  have e3 : ↥(centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh) ≃*
      Multiplicative (ZMod 3) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact mulEquivOfPrimeCardEq (p := 3) hc3 (by rw [Nat.card_eq_fintype_card]; simp)
  exact ⟨e1.trans (e2'.trans (e2.trans (MulEquiv.prodCongr e₀ e3)))⟩

end L192

end CFSG.GH74.Uniqueness.SU.SU7
