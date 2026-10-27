module

public import CFSG.GH74.GLS.Stage1.Thm4.Fstar98

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

theorem commutator_zpowers_eq_of_isPComponent {L : Subgroup X} (hL : IsPComponent 2 L) {u : X}
    (hu : u ∈ normalizer (L : Set X)) (hnle : ¬ ⁅L, zpowers u⁆ ≤ pPrimeCore 2 X) :
    ⁅L, zpowers u⁆ = L := by
  have : (pPrimeCore 2 X).Normal := pPrimeCore_normal
  obtain ⟨Kb, hKb, hLsub, hLmap, hmin⟩ := hL
  set W : Subgroup X := ⁅L, zpowers u⁆ with hW
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hWL : W ≤ L := (le_normalizer_iff_commutator_le_left).1 ((Subgroup.zpowers_le).2 hu)
  have hLnorm : L ≤ normalizer (W : Set X) := normalizer_commutator_ge_left L (zpowers u)
  have hWnorm : (W.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hWL).2 hLnorm
  have hWsub : W.IsSubnormal := Subgroup.IsSubnormal.trans hWL hWnorm.isSubnormal hLsub
  have hWb_le : W.map π ≤ Kb := hLmap ▸ Subgroup.map_mono hWL
  have hclaim : W.map π = Kb := by
    have hbnorm : Kb ≤ normalizer ((W.map π : Subgroup _) : Set _) := by
      rw [← hLmap]
      exact (Subgroup.map_mono hLnorm).trans (Subgroup.le_normalizer_map π)
    have hnorm : ((W.map π).subgroupOf Kb).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWb_le).2 hbnorm
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hKb.1 hnorm with
      htop | hcen
    · refine le_antisymm hWb_le fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Kb) ∈ (W.map π).subgroupOf Kb := by rw [htop]; exact mem_top _
      exact this
    · exfalso
      have hKbperf : ⁅Kb, Kb⁆ = Kb := by
        have h1 : ⁅(⊤ : Subgroup ↥Kb), (⊤ : Subgroup ↥Kb)⁆ = ⊤ := hKb.1.1.commutator_eq_top
        have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥Kb) (⊤ : Subgroup ↥Kb) Kb.subtype
        simp only [h1, Subgroup.map_top, Subgroup.range_subtype] at h2
        exact h2.symm
      have hWeq : W.map π = ⁅Kb, zpowers (π u)⁆ := by
        rw [hW, Subgroup.map_commutator, hLmap, MonoidHom.map_zpowers]
      have hdc : ⁅⁅Kb, zpowers (π u)⁆, Kb⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro y hy
        rw [← hWeq] at hy
        have hyc := hcen (show (⟨y, hWb_le hy⟩ : ↥Kb) ∈ (W.map π).subgroupOf Kb from hy)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have := Subgroup.mem_center_iff.1 hyc ⟨g, hg⟩
        exact congrArg Subtype.val this
      have hbot := CFSG.LocalAnalysis.ComponentInitial.perfect_double_commutator hKbperf hdc
      rw [← hWeq] at hbot
      apply hnle
      intro w hw
      have h1 : π w ∈ W.map π := Subgroup.mem_map_of_mem π hw
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff w).1 h1
  by_contra hne
  exact hmin W (lt_of_le_of_ne hWL hne) hWsub hclaim

end Abstract

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem mem_of_mem_sup_Oz {c : G} (hc : c ∈ Cz z) (hc2 : c ^ 2 = 1) (hmem : c ∈ K ⊔ Oz z) :
    c ∈ K := by
  have h3 := mem_sup_subgroupOf_of_mem h.K_le (c := ⟨c, hc⟩) hmem
  have := h.K_normal_C
  have h2 : (⟨c, hc⟩ : ↥(Cz z)) ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    simpa using hc2
  exact mem_of_mem_sup_odd (K := K.subgroupOf (Cz z)) (N := pPrimeCore 2 ↥(Cz z))
    odd_card_pPrimeCore h2 h3

theorem mem_K_of_comm_le_Oz {u : G} (hu : u ∈ Cz z) (hu2 : u ^ 2 = 1)
    (hcomm : ⁅K, zpowers u⁆ ≤ Oz z) : u ∈ K := by
  have h1 : u ∈ zpowers z ⊔ Oz z := h.fstar_core hu fun k hk =>
    hcomm (Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers u))
  have h2 : u ∈ K ⊔ Oz z := (sup_le_sup_right ((Subgroup.zpowers_le).2 h.z_mem) _) h1
  exact h.mem_of_mem_sup_Oz hu hu2 h2

theorem comm_nle_of_not_mem {u : G} (hu : u ∈ Cz z) (hu2 : u ^ 2 = 1) (huK : u ∉ K) :
    ¬ ⁅K, zpowers u⁆ ≤ pPrimeCoreOf 2 K := fun hle =>
  huK (h.mem_K_of_comm_le_Oz hu hu2 (hle.trans h.pPrimeCoreOf_le_Oz))

theorem comm_eq_of_not_mem {u : G} (hu : u ∈ Cz z) (hu2 : u ^ 2 = 1) (huK : u ∉ K) :
    ⁅K, zpowers u⁆ = K := by
  have hKC := h.K_le
  have hcomp : IsPComponent 2 (K.subgroupOf (Cz z)) := h.std.K_rigid.1.1.2.2.2
  have hnorm : (⟨u, hu⟩ : ↥(Cz z)) ∈
      normalizer ((K.subgroupOf (Cz z) : Subgroup ↥(Cz z)) : Set ↥(Cz z)) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ?_
    have := Subgroup.mem_normalizer_iff.1 (h.mem_normalizer hu) (x : G)
    exact this
  have hnle : ¬ ⁅K.subgroupOf (Cz z), zpowers (⟨u, hu⟩ : ↥(Cz z))⁆ ≤ pPrimeCore 2 ↥(Cz z) := by
    intro hle
    apply huK
    apply h.mem_K_of_comm_le_Oz hu hu2
    have h1 := Subgroup.map_mono (f := (Cz z).subtype) hle
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hKC] at h1
    exact h1
  have h2 := congrArg (Subgroup.map (Cz z).subtype)
    (commutator_zpowers_eq_of_isPComponent hcomp hnorm hnle)
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hKC] at h2
  exact h2

theorem extremal_sylow {u0 : G} (hu0S : u0 ∈ S) (hu02 : orderOf u0 = 2) (hconj : IsConj z u0)
    (hu0K : u0 ∉ K)
    (hmax : ∀ v ∈ S, orderOf v = 2 → IsConj z v → v ∉ K →
      Nat.card ↥(S ⊓ centralizer ({v} : Set G)) ≤ Nat.card ↥(S ⊓ centralizer ({u0} : Set G))) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({u0} : Set G))
      (Cz z ⊓ centralizer ({u0} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : M.Syl2In S (Cz z) := (CFSG.ABGLocalTools.isSylowOf_iff).1 h.std.sylow
  have hAp : IsPGroup 2 ↥(S ⊓ centralizer ({u0} : Set G)) := hSyl.2.1.to_inf_left
  have hAB : S ⊓ centralizer ({u0} : Set G) ≤ Cz z ⊓ centralizer ({u0} : Set G) :=
    inf_le_inf_right _ h.S_le
  obtain ⟨T, hT, hAT⟩ := M.exists_syl2In_ge hAp hAB
  have hTB : T ≤ Cz z ⊓ centralizer ({u0} : Set G) := hT.1
  have hTC : T ≤ Cz z := hTB.trans inf_le_left
  obtain ⟨P, hP, hTP⟩ := M.exists_syl2In_ge hT.2.1 hTC
  obtain ⟨c, hcC, hc⟩ := M.Syl2In.exists_conj hSyl hP
  have hTS : ∀ x ∈ T, c * x * c⁻¹ ∈ S := fun x hx => by
    have hxP : x ∈ P := hTP hx
    rw [hc, M.mem_cj] at hxP
    exact hxP
  have hu0A : u0 ∈ S ⊓ centralizer ({u0} : Set G) :=
    ⟨hu0S, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hu1S : c * u0 * c⁻¹ ∈ S := hTS u0 (hAT hu0A)
  have hu12 : orderOf (c * u0 * c⁻¹) = 2 := by rw [orderOf_conj_eq']; exact hu02
  have hu1conj : IsConj z (c * u0 * c⁻¹) := hconj.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hu1K : c * u0 * c⁻¹ ∉ K := by
    intro hmem
    apply hu0K
    have := (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer (inv_mem hcC)) _).1 hmem
    simpa [mul_assoc] using this
  have hle := hmax _ hu1S hu12 hu1conj hu1K
  have hcard : Nat.card ↥T ≤ Nat.card ↥(S ⊓ centralizer ({c * u0 * c⁻¹} : Set G)) := by
    have hsub : T.map (MulAut.conj c).toMonoidHom ≤ S ⊓ centralizer ({c * u0 * c⁻¹} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxu : x * u0 = u0 * x := Subgroup.mem_centralizer_singleton_iff.1 (hTB hx).2
      refine ⟨hTS x hx, ?_⟩
      show c * x * c⁻¹ ∈ centralizer ({c * u0 * c⁻¹} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * x * c⁻¹ * (c * u0 * c⁻¹) = c * (x * u0) * c⁻¹ := by group
        _ = c * (u0 * x) * c⁻¹ := by rw [hxu]
        _ = c * u0 * c⁻¹ * (c * x * c⁻¹) := by group
    calc Nat.card ↥T = Nat.card ↥(T.map (MulAut.conj c).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hsub
  have hTA : Nat.card ↥T ≤ Nat.card ↥(S ⊓ centralizer ({u0} : Set G)) := hcard.trans hle
  have hTeq : S ⊓ centralizer ({u0} : Set G) = T := Subgroup.eq_of_le_of_card_ge hAT hTA
  rw [hTeq]
  exact (CFSG.ABGLocalTools.isSylowOf_iff).2 hT

theorem z_mem_zStar : z ∈ zStar K := by
  refine ⟨h.z_mem, h.mem_normalizer h.z_cen, ?_, fun k hk => ?_⟩
  · refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => h.pPrimeCoreOf_conj h.z_cen hy,
      fun hy => ?_⟩
    have := h.pPrimeCoreOf_conj (inv_mem h.z_cen) hy
    simpa [mul_assoc] using this
  · have : ⁅k, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (h.z_comm hk)
    rw [this]
    exact one_mem _

end Ctx98

theorem step9_8_inv_of_9_6 (h96 : Lemma9_6) : Step9_8_inv := by
  intro G _ _ Lh _ z t S K hstd hr1 hq1 u hu hu2 hconj
  have h : Ctx98 G Lh z t S K := ⟨hstd, hr1, hq1⟩
  obtain ⟨n, -, -, hcov⟩ := hstd.cover
  by_contra huK
  obtain ⟨u0, ⟨hu0S, hu02, hu0conj, hu0K⟩, hmax⟩ := Set.exists_max_image
    {v : G | v ∈ S ∧ orderOf v = 2 ∧ IsConj z v ∧ v ∉ K}
    (fun v => Nat.card ↥(S ⊓ centralizer ({v} : Set G))) (Set.toFinite _) ⟨u, hu, hu2, hconj, huK⟩
  have hext := h.extremal_sylow hu0S hu02 hu0conj hu0K fun v hv1 hv2 hv3 hv4 =>
    hmax v ⟨hv1, hv2, hv3, hv4⟩
  have hu0sq : u0 ^ 2 = 1 := by
    have := pow_orderOf_eq_one u0
    rwa [hu02] at this
  have hu0C : u0 ∈ Cz z := h.S_le hu0S
  have hKz : Kz Lh z = K := by
    unfold Kz
    rw [hr1]
    exact sSup_singleton
  have hstd' : Std9 G Lh z u0 S K :=
    { toHyp9 := hstd.toHyp9
      z_ord := hstd.z_ord
      t_ord := hu02
      t_cen := hu0C
      K_rigid := hstd.K_rigid
      z_mem := hstd.z_mem
      t_conj := by
        obtain ⟨c, hc⟩ := isConj_iff.1 hu0conj
        refine ⟨c, ?_⟩
        rw [hKz]
        have : c⁻¹ * u0 * c = z := by rw [← hc]; group
        rw [this]
        exact h.z_mem_zStar
      comm_eq := h.comm_eq_of_not_mem hu0C hu0sq hu0K
      comm_nle := h.comm_nle_of_not_mem hu0C hu0sq hu0K
      pref := fun _ K' hK' => by
        rw [hr1, Set.mem_singleton_iff] at hK'
        rw [hK']
        exact h.mem_normalizer hu0C
      sylow := hstd.sylow
      t_mem := hu0S
      t_ext := hext }
  have h' : Ctx98 G Lh z u0 S K := ⟨hstd', hr1, hq1⟩
  exact hu0K (h'.t_mem_K h96 step9_8_fstar hcov)

end CFSG.GH74.GLS.Stage1.Thm4
