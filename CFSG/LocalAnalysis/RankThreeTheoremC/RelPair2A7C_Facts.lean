module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

theorem a7m_isThreeCycle_cOne : cOne.IsThreeCycle := by
  have h : cOne = swap 1 0 * swap 1 2 := by decide
  rw [h]
  exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem a7m_cOne_mem : cOne ∈ alternatingGroup (Fin 7) :=
  eNine_le_alternatingGroup cOne_mem_eNine

theorem a7m_vOne_le : vOne ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨m, rfl⟩
  exact Perm.mem_alternatingGroup.2 (vOneF_spec m).2

theorem a7m_isPretransitive {L : Subgroup (Perm (Fin 7))} {g : Perm (Fin 7)} (hg : g ∈ L)
    (h7 : orderOf g = 7) : MulAction.IsPretransitive L (Fin 7) := by
  have hcyc : g.IsCycle := Perm.isCycle_of_prime_order'' (by simp; norm_num) (by simpa using h7)
  have hsupp : g.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, h7]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : g x ≠ x := Perm.mem_support.1 (hsupp ▸ Finset.mem_univ x)
  have hy : g y ≠ y := Perm.mem_support.1 (hsupp ▸ Finset.mem_univ y)
  obtain ⟨i, hi⟩ := hcyc.exists_pow_eq hx hy
  exact ⟨⟨g ^ i, L.pow_mem hg i⟩, hi⟩

open CFSG.QuasithinUnique.L246.C123 in
theorem a7m_eq_one_of_fix_cOne {U : Type} [CommGroup U] (hcard : Nat.card U = 16)
    (ρ : ↥(alternatingGroup (Fin 7)) →* MulAut U) (hinj : Function.Injective ρ) {u : U}
    (hu : ρ ⟨cOne, a7m_cOne_mem⟩ u = u) : u = 1 := by
  by_contra hne
  have h5 := not_dvd_five_card_stabU ρ hcard hinj hne
  have hmul := orbit_card_mul ρ u
  have hle := ncard_orbU_le ρ hcard hne
  have hidx := index_stabU ρ u
  have htop : stabU ρ u ≠ ⊤ := by
    intro h
    apply h5
    rw [h, Subgroup.card_top, card_A7]
    norm_num
  have h7le : 7 ≤ (orbU ρ u).ncard := hidx ▸ index_ge_seven htop
  have h7 : 7 ∣ Nat.card (stabU ρ u) := by
    set n := (orbU ρ u).ncard
    set s := Nat.card (stabU ρ u)
    interval_cases n <;> omega
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stabU ρ u)) 7 h7
  set L : Subgroup (Perm (Fin 7)) := (stabU ρ u).map (alternatingGroup (Fin 7)).subtype
  have hgL : ((g : A7) : Perm (Fin 7)) ∈ L := ⟨g, g.2, rfl⟩
  have hg7 : orderOf ((g : A7) : Perm (Fin 7)) = 7 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  have := a7m_isPretransitive hgL hg7
  have hprim : MulAction.IsPreprimitive L (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hcL : cOne ∈ L := ⟨⟨cOne, a7m_cOne_mem⟩, mem_stabU.2 hu, rfl⟩
  have hA := Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    a7m_isThreeCycle_cOne hcL
  apply htop
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hA x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem a7m_card_mod_three {U : Type} [Group U] [Finite U] (f : MulAut U) (hf : f ^ 3 = 1)
    (hfix : ∀ u, f u = u → u = 1) (X : Subgroup U) (hX : ∀ x ∈ X, f x ∈ X) :
    Nat.card X % 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite X
  have hf3 : ∀ u, f (f (f u)) = u := fun u => by
    have := congrArg (fun φ : MulAut U => φ u) hf
    simpa [pow_succ, MulAut.mul_apply] using this
  let σ : Perm X := Equiv.subtypeEquiv f.toEquiv (fun u => ⟨fun h => hX u h, fun h => by
      have := hX _ (hX _ h)
      rwa [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, hf3] at this⟩)
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext x
    simp [σ, pow_succ, hf3]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hsupp : σ.supportᶜ = {1} := by
    ext x
    simp only [Finset.mem_compl, Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      exact hfix _ (congrArg Subtype.val h)
    · rintro rfl
      apply Subtype.ext
      simp [σ]
  rw [hsupp, Finset.card_singleton] at hmod
  rw [Nat.card_eq_fintype_card]
  exact hmod.symm

open CFSG.QuasithinUnique.L246.C123 in
theorem a7m_fix_vOne {U : Type} [Group U] (hcomm : ∀ a b : U, a * b = b * a)
    (hcard : Nat.card U = 16) (hU2 : ∀ u : U, u ^ 2 = 1)
    (ρ : ↥(alternatingGroup (Fin 7)) →* MulAut U) (hinj : Function.Injective ρ) :
    ∃ F : Subgroup U, Nat.card F = 4 ∧ ∀ σ : ↥(alternatingGroup (Fin 7)),
      (σ : Perm (Fin 7)) ∈ vOne → σ ≠ 1 → ∀ u : U, ρ σ u = u ↔ u ∈ F := by
  let _ : CommGroup U := { ‹Group U› with mul_comm := hcomm }
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set e : ↥(alternatingGroup (Fin 7)) := ⟨cOne, a7m_cOne_mem⟩
  have he3 : ρ e ^ 3 = 1 := by
    rw [← map_pow]
    have : e ^ 3 = 1 := Subtype.ext (by decide)
    rw [this, map_one]
  have hefix : ∀ u, ρ e u = u → u = 1 := fun u hu => a7m_eq_one_of_fix_cOne hcard ρ hinj hu
  have hclass : ∀ X : Subgroup U, (∀ x ∈ X, ρ e x ∈ X) →
      Nat.card X = 1 ∨ Nat.card X = 4 ∨ Nat.card X = 16 := by
    intro X hX
    have h3 := a7m_card_mod_three (ρ e) he3 hefix X hX
    have hd : Nat.card X ∣ 16 := hcard ▸ Subgroup.card_subgroup_dvd_card X
    have hmem : Nat.card X ∈ Nat.divisors 16 := by simpa using hd
    have e16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [e16] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  let v : Fin 4 → ↥(alternatingGroup (Fin 7)) := fun m => ⟨vOneF m, a7m_vOne_le ⟨m, rfl⟩⟩
  have hve : ∀ m, v m * e = e * v m := fun m => Subtype.ext (vOneF_spec m).1
  have hvv : ∀ m n, v m * v n = v n * v m := fun m n => Subtype.ext (vOneF_comm m n)
  have hv2 : ∀ m, v m * v m = 1 := fun m => Subtype.ext (by
    have := vOneF_sq m
    rw [pow_two] at this
    exact this)
  have hv12 : v 1 * v 2 = v 3 := Subtype.ext (by decide)
  have hv1 : ∀ m, m ≠ 0 → v m ≠ 1 := by
    intro m hm h
    apply hm
    apply vOneF_injective m 0
    have := congrArg Subtype.val h
    exact this.trans (by decide)
  have hcomm' : ∀ a b, a * b = b * a → ∀ x ∈ fixedBy (ρ a), ρ b x ∈ fixedBy (ρ a) := by
    intro a b hab x hx
    rw [mem_fixedBy] at hx ⊢
    rw [← MulAut.mul_apply, ← map_mul, hab, map_mul, MulAut.mul_apply, hx]
  have hinvol : ∀ m (c : U), ρ (v m) (ρ (v m) c) = c := fun m c => by
    rw [← MulAut.mul_apply, ← map_mul, hv2, map_one]
    rfl
  have hfour : ∀ m, m ≠ 0 → Nat.card (fixedBy (ρ (v m))) = 4 := by
    intro m hm
    have hsq := card_le_sq hU2 (ρ (v m)) ⊤ (fun _ _ => trivial) (fun c _ => hinvol m c)
    rw [top_inf_eq, Subgroup.card_top, hcard] at hsq
    have hne : Nat.card (fixedBy (ρ (v m))) ≠ 16 := by
      intro h16
      have htop : fixedBy (ρ (v m)) = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h16, hcard])
      apply hv1 m hm
      apply hinj
      rw [map_one]
      ext u
      have : u ∈ fixedBy (ρ (v m)) := htop ▸ Subgroup.mem_top u
      rw [MulAut.one_apply]
      exact mem_fixedBy.1 this
    rcases hclass _ (hcomm' _ _ (hve m)) with h | h | h
    · rw [h] at hsq
      norm_num at hsq
    · exact h
    · exact absurd h hne
  set F := fixedBy (ρ (v 1)) ⊓ fixedBy (ρ (v 2))
  have hF4 : Nat.card F = 4 := by
    have hsq := card_le_sq hU2 (ρ (v 2)) (fixedBy (ρ (v 1))) (hcomm' _ _ (hvv 1 2))
      (fun c _ => hinvol 2 c)
    rw [hfour 1 (by decide)] at hsq
    have hle : Nat.card F ≤ 4 := hfour 1 (by decide) ▸ Subgroup.card_le_of_le inf_le_left
    have hinv : ∀ x ∈ F, ρ e x ∈ F := fun x hx =>
      ⟨hcomm' _ _ (hve 1) x hx.1, hcomm' _ _ (hve 2) x hx.2⟩
    rcases hclass F hinv with h | h | h
    · rw [h] at hsq
      norm_num at hsq
    · exact h
    · omega
  have hFle : ∀ m, m ≠ 0 → F ≤ fixedBy (ρ (v m)) := by
    intro m hm
    fin_cases m
    · exact absurd rfl hm
    · exact inf_le_left
    · exact inf_le_right
    · intro x hx
      show x ∈ fixedBy (ρ (v 3))
      rw [mem_fixedBy, ← hv12, map_mul, MulAut.mul_apply, mem_fixedBy.1 hx.2, mem_fixedBy.1 hx.1]
  have hFeq : ∀ m, m ≠ 0 → F = fixedBy (ρ (v m)) := fun m hm =>
    Subgroup.eq_of_le_of_card_ge (hFle m hm) (by rw [hfour m hm, hF4])
  refine ⟨F, hF4, fun σ hσ hσ1 u => ?_⟩
  obtain ⟨m, hm⟩ := hσ
  have hσm : σ = v m := Subtype.ext hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hσ1 (hσm.trans (Subtype.ext (by decide)))
  rw [hσm, hFeq m hm0]
  exact mem_fixedBy.symm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7m_mem_normalizer {U : Subgroup G} {j : G}
    (h : U.map (MulAut.conj j).toMonoidHom = U) : j ∈ normalizer (U : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have : j * u * j⁻¹ ∈ U.map (MulAut.conj j).toMonoidHom := ⟨u, hu, rfl⟩
    rwa [h] at this
  · intro hu
    rw [← h] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    have : w = u := by
      simpa [MulAut.conj_apply] using hwu
    exact this ▸ hw

omit [Finite G] in
theorem a7m_exists_rho {H J U : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hJH : J ≤ H)
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7))
    (hUJ : ∀ j ∈ J, U.map (MulAut.conj j).toMonoidHom = U)
    (hker : ∀ j : ↥H, (j : G) ∈ J → ι j = 1 → ∀ u ∈ U, (j : G) * u * (j : G)⁻¹ = u) :
    ∃ ρ : ↥(alternatingGroup (Fin 7)) →* MulAut ↥U, ∀ j : ↥H, (j : G) ∈ J →
      ∀ (hj : ι j ∈ alternatingGroup (Fin 7)) (u : ↥U),
        ((ρ ⟨ι j, hj⟩ u : ↥U) : G) = (j : G) * u * (j : G)⁻¹ := by
  have hJN : J ≤ normalizer (U : Set G) := fun j hj => a7m_mem_normalizer (hUJ j hj)
  let c : ↥J →* MulAut ↥U := U.normalizerMonoidHom.comp (Subgroup.inclusion hJN)
  have hmem : ∀ j : ↥J, ι (Subgroup.inclusion hJH j) ∈ alternatingGroup (Fin 7) := fun j => by
    rw [← hJι]
    exact ⟨_, j.2, rfl⟩
  let f : ↥J →* ↥(alternatingGroup (Fin 7)) :=
    (ι.comp (Subgroup.inclusion hJH)).codRestrict _ hmem
  have hf : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    rw [← hJι] at hσ
    obtain ⟨h, hh, rfl⟩ := hσ
    exact ⟨⟨h, hh⟩, rfl⟩
  have hle : f.ker ≤ c.ker := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj ⊢
    have h1 : ι (Subgroup.inclusion hJH j) = 1 := congrArg Subtype.val hj
    ext u
    have := hker (Subgroup.inclusion hJH j) j.2 h1 u u.2
    simpa [c] using this
  refine ⟨f.liftOfSurjective hf ⟨c, hle⟩, fun j hjJ hj u => ?_⟩
  have hfj : f ⟨j, hjJ⟩ = ⟨ι j, hj⟩ := rfl
  rw [← hfj, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem a7m_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K T : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hKP : K ≤ normalizer (P : Set G)) (hTK : T ≤ K)
    (hT : IsPGroup p T) : T ≤ P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hQn : (Q : Subgroup K).Normal := by
    rw [hQ]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP.le).mpr hKP
  have hT' : IsPGroup p (T.subgroupOf K) := hT.comap_subtype
  obtain ⟨Q', hTQ'⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have hQQ' : Q' = Q := by
    rw [← hg]
    exact Sylow.smul_eq_of_normal
  intro x hx
  have h2 := hTQ' (show (⟨x, hTK hx⟩ : K) ∈ T.subgroupOf K from hx)
  rw [hQQ', hQ] at h2
  exact h2

theorem A7Frame.module_facts {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {J U : Subgroup G} (hJH : J ≤ H)
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7))
    (hUJ : ∀ j ∈ J, U.map (MulAut.conj j).toMonoidHom = U) (hU : IsElemAbelian 2 U)
    (hU16 : Nat.card U = 16) (hUC : U ⊓ centralizer (J : Set G) = ⊥)
    (hker : ∀ j : ↥H, (j : G) ∈ J → ι j = 1 → ∀ u ∈ U, (j : G) * u * (j : G)⁻¹ = u)
    (hVJ : V ≤ J ⊔ pCoreOf 2 H) (hUS : U ≤ centralizer (pCoreOf 2 H : Set G)) :
    V ⊓ centralizer (U : Set G) = pCoreOf 2 H ∧
      (∀ x ∈ V, x ∉ pCoreOf 2 H →
        U ⊓ centralizer ({x} : Set G) = U ⊓ centralizer (V : Set G)) ∧
      Nat.card U = 4 * Nat.card (U ⊓ centralizer (V : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρ⟩ := a7m_exists_rho hJH hJι hUJ hker
  have hJA : ∀ j : ↥H, (j : G) ∈ J → ι j ∈ alternatingGroup (Fin 7) := fun j hj =>
    hJι ▸ ⟨j, hj, rfl⟩
  have hinj : Function.Injective ρ := by
    have := CFSG.QuasithinUnique.L246.C123.isSimple_A7
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ).1 h
    · exfalso
      have hle : U ≤ U ⊓ centralizer (J : Set G) := by
        intro u hu
        refine ⟨hu, mem_centralizer_iff.2 fun j hj => ?_⟩
        have h1 : ρ ⟨ι ⟨j, hJH hj⟩, hJA ⟨j, hJH hj⟩ hj⟩ = 1 :=
          (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
        have h2 := hρ ⟨j, hJH hj⟩ hj (hJA _ hj) ⟨u, hu⟩
        rw [h1] at h2
        have h3 : u = j * u * j⁻¹ := h2
        calc j * u = j * u * j⁻¹ * j := by group
          _ = u * j := by rw [← h3]
      rw [hUC, le_bot_iff] at hle
      have h1 : Nat.card U = 1 := by rw [hle, Subgroup.card_bot]
      omega
  have hK : ∀ h : ↥H, ι h = 1 → (h : G) ∈ a7K H := fun h h1 => by
    have : h ∈ ι.ker := h1
    rw [hF.ker_eq] at this
    exact ⟨h, this, rfl⟩
  have hι1 : ∀ h : ↥H, (h : G) ∈ a7K H → ι h = 1 := by
    rintro h ⟨k, hk, hkh⟩
    have hkh' : k = h := Subtype.ext hkh
    rw [← hkh']
    have : k ∈ ι.ker := hF.ker_eq ▸ hk
    exact this
  have hVK : V ⊓ a7K H ≤ pCoreOf 2 H :=
    a7m_le_of_isSylowOf hF.sylow ((a7K_le H).trans hF.H_norm.ge) inf_le_right
      (hF.V_two.to_le inf_le_left)
  have hact : ∀ v (hv : v ∈ V), ∃ σ : ↥(alternatingGroup (Fin 7)),
      (σ : Perm (Fin 7)) = ι ⟨v, hF.V_le hv⟩ ∧
        ∀ u : ↥U, v * (u : G) * v⁻¹ = ((ρ σ u : ↥U) : G) := by
    intro v hv
    have hv' : v ∈ ((J ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hVJ hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J _ (hJH.trans hF.H_norm.ge)] at hv'
    obtain ⟨j, hj, s, hs, rfl⟩ := hv'
    have hsH : s ∈ H := Subgroup.map_subtype_le _ hs
    have hjH := hJH hj
    refine ⟨⟨ι ⟨j, hjH⟩, hJA ⟨j, hjH⟩ hj⟩, ?_, fun u => ?_⟩
    · have : (⟨j * s, hF.V_le hv⟩ : ↥H) = ⟨j, hjH⟩ * ⟨s, hsH⟩ := rfl
      rw [this, map_mul, hι1 ⟨s, hsH⟩ (hF.sylow.le hs), mul_one]
    · rw [hρ ⟨j, hjH⟩ hj]
      have hsu : s * (u : G) = u * s := mem_centralizer_iff.1 (hUS u.2) s hs
      calc j * s * u * (j * s)⁻¹ = j * (s * u) * s⁻¹ * j⁻¹ := by group
        _ = j * (u * s) * s⁻¹ * j⁻¹ := by rw [hsu]
        _ = j * u * j⁻¹ := by group
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hU.2 u u.2)
  obtain ⟨F, hF4, hFσ⟩ := a7m_fix_vOne hU.1.is_comm.comm hU16 hU2 ρ hinj
  have hσV : ∀ v (hv : v ∈ V), ι ⟨v, hF.V_le hv⟩ ∈ vOne := fun v hv => by
    rw [← hF.V_img]
    exact ⟨⟨v, hF.V_le hv⟩, hv, rfl⟩
  have hcentV : ∀ u : ↥U, (u : G) ∈ centralizer (V : Set G) ↔ u ∈ F := by
    intro u
    constructor
    · intro hu
      obtain ⟨h, hh, hh1⟩ : vOneF 1 ∈ (V.subgroupOf H).map ι := hF.V_img ▸ ⟨1, rfl⟩
      obtain ⟨σ, hσ, hσu⟩ := hact h hh
      have hσ1 : σ ≠ 1 := by
        intro h1
        have : vOneF 1 = vOneF 0 := by
          rw [← hh1, ← hσ, h1]
          rfl
        exact absurd (vOneF_injective 1 0 this) (by decide)
      refine (hFσ σ (hσ ▸ hσV h hh) hσ1 u).1 (Subtype.ext ?_)
      rw [← hσu u, mem_centralizer_iff.1 hu h hh]
      group
    · intro hu
      rw [mem_centralizer_iff]
      intro v hv
      obtain ⟨σ, hσ, hσu⟩ := hact v hv
      have hfix : ρ σ u = u := by
        by_cases hσ1 : σ = 1
        · rw [hσ1, map_one]
          rfl
        · exact (hFσ σ (hσ ▸ hσV v hv) hσ1 u).2 hu
      have h2 := hσu u
      rw [hfix] at h2
      calc v * u = v * u * v⁻¹ * v := by group
        _ = u * v := by rw [h2]
  have hmapF : F.map U.subtype = U ⊓ centralizer (V : Set G) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, (hcentV u).2 hu⟩
    · rintro ⟨hgU, hgV⟩
      exact ⟨⟨g, hgU⟩, (hcentV ⟨g, hgU⟩).1 hgV, rfl⟩
  refine ⟨?_, fun x hx hxS => ?_, ?_⟩
  · apply le_antisymm
    · rintro v ⟨hv, hvU⟩
      obtain ⟨σ, hσ, hσu⟩ := hact v hv
      have hσ1 : σ = 1 := by
        apply hinj
        rw [map_one]
        ext u
        rw [← hσu u]
        have := mem_centralizer_iff.1 hvU u u.2
        show v * u * v⁻¹ = u
        rw [← this]
        group
      apply hVK
      refine ⟨hv, hK ⟨v, hF.V_le hv⟩ ?_⟩
      rw [← hσ, hσ1]
      rfl
    · intro s hs
      exact ⟨hF.S_le hs, mem_centralizer_iff.2 fun u hu =>
        (mem_centralizer_iff.1 (hUS hu) s hs).symm⟩
  · obtain ⟨σ, hσ, hσu⟩ := hact x hx
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hxS
      apply hVK
      refine ⟨hx, hK ⟨x, hF.V_le hx⟩ ?_⟩
      rw [← hσ, h1]
      rfl
    apply le_antisymm
    · rintro u ⟨hu, hux⟩
      refine ⟨hu, (hcentV ⟨u, hu⟩).2
        ((hFσ σ (hσ ▸ hσV x hx) hσ1 ⟨u, hu⟩).1 (Subtype.ext ?_))⟩
      rw [← hσu ⟨u, hu⟩]
      have := mem_centralizer_iff.1 hux x rfl
      show x * u * x⁻¹ = u
      rw [this]
      group
    · exact inf_le_inf_left U (centralizer_le (Set.singleton_subset_iff.2 hx))
  · rw [← hmapF, Subgroup.card_map_of_injective U.subtype_injective, hF4, hU16]

end CFSG.LocalAnalysis.RankThreeTheoremC
