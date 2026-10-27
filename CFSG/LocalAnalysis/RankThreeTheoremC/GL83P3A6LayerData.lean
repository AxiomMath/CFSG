module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod CFSG.ComponentClassification

section Components

variable {X : Type} [Group X] [Finite X]

theorem inf_eq_bot_of_le_centralizer (hfree : SolvableRadical.Free X) {L A : Subgroup X}
    (hL : IsComponentOf L ⊤) (hA : A ≤ centralizer (L : Set X)) : A ⊓ L = ⊥ := by
  have hZ := RadicalFreeLayer.component_center_eq_bot hfree L hL
  rw [eq_bot_iff]
  intro a ha
  have hc : (⟨a, (mem_inf.mp ha).2⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp (hA (mem_inf.mp ha).1) l l.2)
  rw [hZ, mem_bot] at hc
  exact mem_bot.mpr (congrArg Subtype.val hc)

theorem le_centralizer_of_ne {L L' : Subgroup X} (hL : IsComponentOf L ⊤)
    (hL' : IsComponentOf L' ⊤) (hne : L ≠ L') : L ≤ centralizer (L' : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (LocalComponents.commute_of_ne L L' hL hL' hne)

theorem isComponent_map_conj {L : Subgroup X} (hL : IsComponentOf L ⊤) (g : X) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL

theorem mem_normalizer_iff_map_conj {L : Subgroup X} {g : X} :
    g ∈ normalizer (L : Set X) ↔ L.map (MulAut.conj g).toMonoidHom = L :=
  CommutingComponentFamily.normalizer_iff_conjugate_eq L g

theorem component_not_comm {L : Subgroup X} (hL : IsComponentOf L ⊤) : ¬ IsMulCommutative ↥L := by
  intro hc
  have hnt : Nontrivial ↥L := Quasisimple.nontrivial hL.2.2
  have hperf : commutator ↥L = ⊤ := hL.2.2.1
  have hbot : commutator ↥L = ⊥ := (commutator_eq_bot_iff ↥L).mpr hc
  rw [hbot] at hperf
  obtain ⟨a, b, hab⟩ := hnt
  have ha : a ∈ (⊥ : Subgroup ↥L) := hperf ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup ↥L) := hperf ▸ mem_top b
  rw [mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

theorem not_isPSolvable_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ¬ IsMulCommutative S) (h3 : 3 ∣ Nat.card S) : ¬ CFSG.HallHigman.IsPSolvable 3 S := by
  intro hsolv
  haveI := hS
  have hsimple : IsSimpleGroup (↥(⊤ : Subgroup S) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup S))) :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)
  have hidx : (⊥ : Subgroup ↥(⊤ : Subgroup S)).index = Nat.card S := by
    rw [Subgroup.index_bot, Nat.card_congr Subgroup.topEquiv.toEquiv]
  rcases hsolv ⊤ (Subgroup.Normal.isSubnormal inferInstance) ⊥ hsimple with h | h
  · rw [hidx] at h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic S := isCyclic_of_prime_card (p := 3) h
    exact hnc ⟨⟨fun a b => mul_comm a b⟩⟩
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h h3

end Components

structure XData (X : Type) [Group X] [Finite X] (P : Subgroup X) (x e₂ e₃ t ρ : X) (s : ℤ) :
    Prop where
  frame : XFrame x e₂ e₃ t ρ s
  sylow : IsSylowOf 3 P ⊤
  card : Nat.card P = 81
  Q_le : Qf x e₂ e₃ ≤ P
  t_mem : t ∈ P
  cent : ∀ g ∈ P, g * x = x * g → g ∈ Qf x e₂ e₃
  core : ∀ N : Subgroup X, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥
  no3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → ¬ Qf x e₂ e₃ ≤ N
  solv : CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X))

namespace XData

variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {x e₂ e₃ t ρ : X} {s : ℤ}
  (hd : XData X P x e₂ e₃ t ρ s)

include hd

theorem P_norm : P ≤ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  have h1 := Subgroup.relIndex_mul_card (H := Qf x e₂ e₃) (K := P)
  rw [inf_of_le_left hd.Q_le, hd.frame.Q_card, hd.card] at h1
  have hidx : (Qf x e₂ e₃).relIndex P = 3 := by omega
  have hn : ((Qf x e₂ e₃).subgroupOf P).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    have : ((Qf x e₂ e₃).subgroupOf P).index = 3 := hidx
    rw [this, show Nat.card ↥P = 81 from hd.card]
    norm_num
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hd.Q_le).mp hn

theorem t_cube_mem : t * t * t ∈ Qf x e₂ e₃ := by
  have hf := hd.frame
  refine hd.cent _ (P.mul_mem (P.mul_mem hd.t_mem hd.t_mem) hd.t_mem) ?_
  have e : (t * t * t) * x * (t * t * t)⁻¹ = x := by
    rw [show (t * t * t) * x * (t * t * t)⁻¹ = t * (t * (t * x * t⁻¹) * t⁻¹) * t⁻¹ by group,
      hf.t_x, hf.t_e₂, hf.t_e₃]
  calc t * t * t * x = ((t * t * t) * x * (t * t * t)⁻¹) * (t * t * t) := by group
    _ = x * (t * t * t) := by rw [e]

theorem Q_ne_bot : Qf x e₂ e₃ ≠ ⊥ := by
  intro h
  have := hd.frame.x_mem
  rw [h, mem_bot] at this
  exact hd.frame.x_ne this

theorem le_of_normal (N : Subgroup X) (hN : N.Normal) (hne : N ≠ ⊥) : Qf x e₂ e₃ ≤ N := by
  have hf := hd.frame
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card N := by
    by_contra h3
    exact hne (hd.core N hN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
  have hSyl : IsSylowOf 3 (P ⊓ N) N :=
    hd.sylow.inf_of_le_normalizer le_top (fun g _ => (normalizer_eq_top_iff.mpr hN).ge (mem_top g))
  have hne' : P ⊓ N ≠ ⊥ := by
    intro hbot
    rw [isSylowOf_iff] at hSyl
    obtain ⟨-, -, hdvd⟩ := hSyl
    rw [hbot, Subgroup.relIndex_bot_left] at hdvd
    exact hdvd h3
  have hQn : Qf x e₂ e₃ ≤ normalizer ((P ⊓ N : Subgroup X) : Set X) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro g
    have hqP : q ∈ P := hd.Q_le hq
    constructor
    · intro hg
      exact mem_inf.mpr ⟨P.mul_mem (P.mul_mem hqP (mem_inf.mp hg).1) (P.inv_mem hqP),
        hN.conj_mem _ (mem_inf.mp hg).2 q⟩
    · intro hg
      have h1 := mem_inf.mp hg
      have e : g = q⁻¹ * (q * g * q⁻¹) * q := by group
      rw [e]
      exact mem_inf.mpr ⟨P.mul_mem (P.mul_mem (P.inv_mem hqP) h1.1) hqP,
        by simpa using hN.conj_mem _ h1.2 q⁻¹⟩
  have hmeet := hf.inf_ne_bot hd.cent hd.P_norm inf_le_left hne' hQn
  have hW : N ⊓ Qf x e₂ e₃ ≠ ⊥ := by
    intro hb
    apply hmeet
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ N ⊓ Qf x e₂ e₃ := mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hg).1).2, (mem_inf.mp hg).2⟩
    rwa [hb] at this
  have hinv : ∀ g ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X), ∀ w ∈ N ⊓ Qf x e₂ e₃,
      g * w * g⁻¹ ∈ N ⊓ Qf x e₂ e₃ := fun g hg w hw =>
    mem_inf.mpr ⟨hN.conj_mem _ (mem_inf.mp hw).1 g,
      hf.conj_mem_of_mem_normalizer hg (mem_inf.mp hw).2⟩
  rcases hf.eq_bot_or_eq_of_invariant inf_le_right (hinv t hf.t_mem_normalizer)
    (hinv ρ hf.ρ_mem_normalizer) with hb | heq
  · exact absurd hb hW
  · rw [← heq]
    exact inf_le_left

theorem free : SolvableRadical.Free X := by
  intro N hN hsolv
  by_contra hne
  haveI : N.Normal := hN
  obtain ⟨A, hAN, hA⟩ := MinimalNormal.exists_le N hne
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAN)
  obtain ⟨r, hr, -, hAr⟩ := MinimalNormal.elementaryAbelian_of_solvable A hA
  have hAn : A.Normal := hA.prop.1
  have hAne : A ≠ ⊥ := hA.prop.2
  by_cases hr3 : r = 3
  · subst hr3
    exact hd.no3 A hAn hAr (hd.le_of_normal A hAn hAne)
  · haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAr
    refine hAne (hd.core A hAn ?_)
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3))

theorem nontrivial : Nontrivial X :=
  ⟨⟨x, 1, hd.frame.x_ne⟩⟩

theorem component_le {L : Subgroup X} (hL : IsComponentOf L ⊤) (N : Subgroup X) (hN : N.Normal)
    (hne : N ≠ ⊥) : L ≤ N := by
  haveI : N.Normal := hN
  rcases LocalComponents.normal_contains_or_commutes L N hL with hle | hcomm
  · exact hle
  · exfalso
    have hLC : L ≤ centralizer (N : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hCne : centralizer (N : Set X) ≠ ⊥ := by
      intro hb
      have hnt : Nontrivial ↥L := Quasisimple.nontrivial hL.2.2
      have : L = ⊥ := le_bot_iff.mp (hb ▸ hLC)
      exact (L.nontrivial_iff_ne_bot.mp hnt) this
    have hQC := hd.le_of_normal (centralizer (N : Set X)) inferInstance hCne
    have hQN := hd.le_of_normal N hN hne
    have hZn : (N ⊓ centralizer (N : Set X)).Normal := inferInstance
    have hZc : IsMulCommutative ↥(N ⊓ centralizer (N : Set X)) := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exact mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (mem_inf.mp a.2).1
    have hsolv : Group.IsSolvable ↥(N ⊓ centralizer (N : Set X)) :=
      Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (mem_inf.mp a.2).1))
    have hbot := hd.free _ hZn hsolv
    exact hd.Q_ne_bot (le_bot_iff.mp (hbot ▸ le_inf hQN hQC))

theorem layer_ne_bot : Layer.subgroup X ≠ ⊥ := by
  haveI := hd.nontrivial
  obtain ⟨L, hL⟩ := RadicalFreeLayer.exists_component hd.free
  intro hb
  have hnt : Nontrivial ↥L := Quasisimple.nontrivial hL.2.2
  exact (L.nontrivial_iff_ne_bot.mp hnt) (le_bot_iff.mp (hb ▸ Layer.component_le hL))

theorem Q_le_layer : Qf x e₂ e₃ ≤ Layer.subgroup X :=
  hd.le_of_normal _ (Layer.normal X) hd.layer_ne_bot

theorem Q_le_normalizer {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    Qf x e₂ e₃ ≤ normalizer (L : Set X) :=
  hd.Q_le_layer.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (Layer.component_le hL)).mp
    (Layer.normal_component hL))

theorem exists_component_three : ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ 3 ∣ Nat.card L := by
  classical
  by_contra hcon
  push Not at hcon
  let ι := {L : Subgroup X // IsComponentOf L ⊤}
  haveI : Fintype ι := Fintype.ofFinite ι
  let H : ι → Subgroup X := fun i => i.1
  have hcomm : Pairwise fun i j : ι => ∀ a b : X, a ∈ H i → b ∈ H j → Commute a b := by
    intro i j hij a b ha hb
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    exact ((mem_centralizer_iff.mp (le_centralizer_of_ne i.2 j.2 hne ha)) b hb).symm
  have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
  have hE : (⨆ i : ι, H i) = Layer.subgroup X := by
    rw [Layer.subgroup.eq_sSup, sSup_eq_iSup']
    rfl
  have hdvd : Nat.card (Layer.subgroup X) ∣ ∏ i : ι, Nat.card (H i) := by
    rw [← hE, ← hrange, ← Nat.card_pi]
    exact Subgroup.card_range_dvd _
  have h27 : Nat.card (Qf x e₂ e₃) ∣ Nat.card (Layer.subgroup X) :=
    Subgroup.card_dvd_of_le hd.Q_le_layer
  rw [hd.frame.Q_card] at h27
  have h3 : 3 ∣ ∏ i : ι, Nat.card (H i) :=
    (dvd_trans ⟨9, by norm_num⟩ h27).trans hdvd
  obtain ⟨i, -, hi⟩ := (Nat.prime_three.prime.dvd_finsetProd_iff _).mp h3
  exact hcon i.1 i.2 hi

theorem inf_ne_bot_of_three {L : Subgroup X} (hL : IsComponentOf L ⊤) (h3 : 3 ∣ Nat.card L) :
    Qf x e₂ e₃ ⊓ L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Layer.subgroup X with hEdef
  have hEn : E.Normal := Layer.normal X
  have hLE : L ≤ E := Layer.component_le hL
  have hEL : E ≤ normalizer (L : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLE).mp (Layer.normal_component hL)
  have hPE : IsSylowOf 3 (P ⊓ E) E :=
    hd.sylow.inf_of_le_normalizer le_top (fun g _ => (normalizer_eq_top_iff.mpr hEn).ge (mem_top g))
  have hPL : IsSylowOf 3 ((P ⊓ E) ⊓ L) L := hPE.inf_of_le_normalizer hLE hEL
  have hne : (P ⊓ E) ⊓ L ≠ ⊥ := by
    intro hbot
    rw [isSylowOf_iff] at hPL
    obtain ⟨-, -, hdvd⟩ := hPL
    rw [hbot, Subgroup.relIndex_bot_left] at hdvd
    exact hdvd h3
  have hQn : Qf x e₂ e₃ ≤ normalizer (((P ⊓ E) ⊓ L : Subgroup X) : Set X) := by
    intro q hq
    have hqP : q ∈ P := hd.Q_le hq
    have hqL : q ∈ normalizer (L : Set X) := hd.Q_le_normalizer hL hq
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨⟨hgP, hgE⟩, hgL⟩ := hg
      exact ⟨⟨P.mul_mem (P.mul_mem hqP hgP) (P.inv_mem hqP), hEn.conj_mem _ hgE q⟩,
        (mem_normalizer_iff.mp hqL g).mp hgL⟩
    · intro hg
      obtain ⟨⟨hgP, hgE⟩, hgL⟩ := hg
      have e : g = q⁻¹ * (q * g * q⁻¹) * q := by group
      rw [e]
      refine ⟨⟨P.mul_mem (P.mul_mem (P.inv_mem hqP) hgP) hqP,
        by simpa using hEn.conj_mem _ hgE q⁻¹⟩, ?_⟩
      have := (mem_normalizer_iff.mp ((normalizer _).inv_mem hqL) (q * g * q⁻¹)).mp hgL
      simpa using this
  have hmeet := hd.frame.inf_ne_bot hd.cent hd.P_norm (inf_le_left.trans inf_le_left) hne hQn
  intro hbot
  apply hmeet
  rw [eq_bot_iff]
  intro g hg
  have : g ∈ Qf x e₂ e₃ ⊓ L := mem_inf.mpr ⟨(mem_inf.mp hg).2, (mem_inf.mp hg).1.2⟩
  rwa [hbot] at this

end XData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
