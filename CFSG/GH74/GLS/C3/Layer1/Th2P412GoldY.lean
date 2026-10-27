module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldBender
import CFSG.Goldschmidt.Steps.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.LocalAnalysis.ComponentClassification.ComponentAutomorphisms

public section

namespace CFSG.GH74.GLS.Th2.P412

namespace GoldY

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem omega1_map {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    (P : Subgroup A) : Omega1 (P.map f) = (Omega1 P).map f := by
  rw [Omega1, Omega1, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hxP, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxP, ?_⟩, rfl⟩
    apply hf
    rw [map_pow, hy2, map_one]
  · rintro ⟨x, ⟨hxP, hx2⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, by rw [← map_pow, hx2, map_one]⟩

theorem card_omega1_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (P : Subgroup A) :
    Nat.card (Omega1 (P.map f)) = Nat.card (Omega1 P) := by
  rw [omega1_map f hf, Subgroup.card_map_of_injective hf]

theorem omega1_mono {G : Type*} [Group G] {P Q : Subgroup G} (h : P ≤ Q) :
    Omega1 P ≤ Omega1 Q :=
  Subgroup.closure_mono fun _ ht => ⟨h ht.1, ht.2⟩

theorem isMulCommutative_of_le {G : Type*} [Group G] {H N : Subgroup G} (hHN : H ≤ N)
    (hN : IsMulCommutative N) : IsMulCommutative H :=
  ⟨⟨fun a b => Subtype.ext (by
    have h := hN.is_comm.comm ⟨a, hHN a.2⟩ ⟨b, hHN b.2⟩
    exact congrArg (fun x : N => (x : G)) h)⟩⟩

theorem isMulCommutative_of_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {H : Subgroup A} (h : IsMulCommutative (H.map f)) :
    IsMulCommutative H :=
  ⟨⟨fun a b => Subtype.ext (hf (by
    have h2 := congrArg Subtype.val (h.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
    simpa [map_mul] using h2))⟩⟩

theorem exists_sylow_quotient {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]
    (hZ : Subgroup.center ↥K = ⊥) (T : Sylow 2 Y) :
    ∃ TQ : Sylow 2 (↥K ⧸ Subgroup.center ↥K),
      Nat.card (TQ : Subgroup (↥K ⧸ Subgroup.center ↥K)) = Nat.card ↥((T : Subgroup Y) ⊓ K) ∧
      Nat.card (Omega1 (TQ : Subgroup (↥K ⧸ Subgroup.center ↥K))) =
        Nat.card (Omega1 ((T : Subgroup Y) ⊓ K)) ∧
      (IsMulCommutative (Omega1 (T : Subgroup Y)) →
        IsMulCommutative (Omega1 (TQ : Subgroup (↥K ⧸ Subgroup.center ↥K)))) := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, T.isPGroup', by rw [Subgroup.relIndex_top_right]; exact T.not_dvd_index⟩
  obtain ⟨S, hS⟩ := hT.inf_of_le_normalizer (N := K) le_top
    (by rw [Subgroup.normalizer_eq_top])
  have hπinj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hπsurj := QuotientGroup.mk'_surjective (Subgroup.center ↥K)
  refine ⟨S.mapSurjective hπsurj, ?_, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective, Subgroup.card_map_of_injective hπinj, ← hS,
      Subgroup.card_map_of_injective K.subtype_injective]
  · rw [Sylow.coe_mapSurjective, card_omega1_map _ hπinj, ← hS,
      card_omega1_map _ K.subtype_injective]
  · intro hcomm
    rw [Sylow.coe_mapSurjective, omega1_map _ hπinj]
    refine isMulCommutative_map ?_ _
    refine isMulCommutative_of_map K.subtype K.subtype_injective ?_
    rw [← omega1_map _ K.subtype_injective, hS]
    exact isMulCommutative_of_le (omega1_mono inf_le_left) hcomm

theorem center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO2 : CFSG.Open.pCore 2 Y = ⊥) (hO2' : goldschmidtOddCore Y = ⊥)
    (hlayer : goldschmidtLayer Y = ⊤) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzL : z ∈ goldschmidtLayer Y := by rw [hlayer]; exact Subgroup.mem_top z
  have hmem : z ∈ (Subgroup.center (goldschmidtLayer Y)).map (goldschmidtLayer Y).subtype :=
    ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr fun w => Subtype.ext
      (Subgroup.mem_center_iff.mp hz w), rfl⟩
  have h := (N8d Y hO2').2.1 hmem
  rwa [hO2] at h

theorem component_center_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hZ : Subgroup.center Y = ⊥) (hlayer : goldschmidtLayer Y = ⊤)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : Subgroup.center ↥K = ⊥ := by
  have hle := CFSG.ComponentClassification.ComponentAutomorphisms.center_le_center_of_layer_top
    hlayer K hK
  rw [hZ] at hle
  rw [eq_bot_iff]
  intro z hz
  have h : K.subtype z ∈ (⊥ : Subgroup Y) := hle (Subgroup.mem_map_of_mem _ hz)
  rw [Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

theorem component_normal {Y : Type} [Group Y] [Finite Y] (hlayer : goldschmidtLayer Y = ⊤)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : K.Normal := by
  have hn := CFSG.ComponentClassification.Layer.normal_component hK
  have hle : K ≤ CFSG.ComponentClassification.Layer.subgroup Y :=
    CFSG.ComponentClassification.Layer.component_le hK
  rw [Subgroup.normal_subgroupOf_iff hle] at hn
  refine ⟨fun n hn' g => hn n g hn' ?_⟩
  have h : CFSG.ComponentClassification.Layer.subgroup Y = ⊤ := hlayer
  rw [h]
  exact Subgroup.mem_top g

theorem inf_component_eq_bot {Y : Type} [Group Y] [Finite Y] {K L : Subgroup Y}
    (hKL : K ≠ L) (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hZK : Subgroup.center ↥K = ⊥) : K ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxL⟩
  have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hL hKL)
  have hxc : (⟨x, hxK⟩ : K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcomm k.2) x hxL).symm
  rw [hZK, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

theorem omega1_le_component (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    {K : Subgroup Y} [K.Normal] (hZ : Subgroup.center ↥K = ⊥) (hK : IsComponentOf K ⊤)
    (hc : goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K))
    (T : Sylow 2 Y) (hV : Nat.card (Omega1 (T : Subgroup Y)) = 4)
    (hVcomm : IsMulCommutative (Omega1 (T : Subgroup Y))) :
    Omega1 (T : Subgroup Y) ≤ K := by
  obtain ⟨TQ, -, hcardΩ, hcomm⟩ := exists_sylow_quotient K hZ T
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  have h4 := (hN11b _ hc TQ (hcomm hVcomm)).1
  rw [hcardΩ] at h4
  have hle : Omega1 ((T : Subgroup Y) ⊓ K) ≤ Omega1 (T : Subgroup Y) :=
    omega1_mono inf_le_left
  have heq : Omega1 ((T : Subgroup Y) ⊓ K) = Omega1 (T : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hV]; exact h4)
  calc Omega1 (T : Subgroup Y) = Omega1 ((T : Subgroup Y) ⊓ K) := heq.symm
    _ ≤ (T : Subgroup Y) ⊓ K := CFSG.Goldschmidt.GoldType.omega1_le _
    _ ≤ K := inf_le_right

theorem exists_component_eq_top (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    (hO2 : CFSG.Open.pCore 2 Y = ⊥) (hO2' : goldschmidtOddCore Y = ⊥)
    (hlayer : goldschmidtLayer Y = ⊤)
    (hc : ∀ K : Subgroup Y, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (T : Sylow 2 Y) (hV : Nat.card (Omega1 (T : Subgroup Y)) = 4)
    (hVcomm : IsMulCommutative (Omega1 (T : Subgroup Y))) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ K = ⊤ := by
  have hZY := center_eq_bot hO2 hO2' hlayer
  have hΩ : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Omega1 (T : Subgroup Y) ≤ K := fun K hK =>
    have := component_normal hlayer hK
    omega1_le_component hN11b (component_center_eq_bot hZY hlayer hK) hK (hc K hK) T hV hVcomm
  have hne : Omega1 (T : Subgroup Y) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV
    exact absurd hV (by norm_num)
  obtain ⟨K₀, hK₀⟩ : ∃ K : Subgroup Y, IsComponentOf K ⊤ := by
    by_contra hno
    push Not at hno
    have hbot : goldschmidtLayer Y = ⊥ :=
      le_antisymm (sSup_le fun K hK => (hno K hK).elim) bot_le
    refine hne (le_antisymm (fun x _ => ?_) bot_le)
    rw [← hbot, hlayer]
    exact Subgroup.mem_top x
  have huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K₀ := by
    intro L hL
    by_contra hLK
    have hbot : K₀ ⊓ L = ⊥ :=
      inf_component_eq_bot (Ne.symm hLK) hK₀ hL (component_center_eq_bot hZY hlayer hK₀)
    exact hne (le_antisymm (hbot ▸ le_inf (hΩ K₀ hK₀) (hΩ L hL)) bot_le)
  refine ⟨K₀, hK₀, ?_⟩
  rw [eq_top_iff, ← hlayer]
  exact sSup_le fun L hL => (huniq L hL).le

end GoldY

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem sylow_card_of_layer
    (hN11a : S_N11a) (hN11b : S_N11b)
    {Y : Type} [Group Y] [Finite Y]
    (hO2 : CFSG.Open.pCore 2 Y = ⊥) (hO2' : goldschmidtOddCore Y = ⊥)
    (hlayer : goldschmidtLayer Y = ⊤)
    (hc : ∀ K : Subgroup Y, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (T : Sylow 2 Y) (hV : Nat.card (Omega1 (T : Subgroup Y)) = 4)
    (hVcomm : IsMulCommutative (Omega1 (T : Subgroup Y))) :
    Nat.card (T : Subgroup Y) = 4 ∨ Nat.card (T : Subgroup Y) = 64 := by
  obtain ⟨K, hK, rfl⟩ := GoldY.exists_component_eq_top hN11b hO2 hO2' hlayer hc T hV hVcomm
  have hZ := GoldY.component_center_eq_bot (GoldY.center_eq_bot hO2 hO2' hlayer) hlayer hK
  obtain ⟨TQ, hcardT, hcardΩ, hcomm⟩ := GoldY.exists_sylow_quotient (⊤ : Subgroup Y) hZ T
  have : IsSimpleGroup (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)) := hK.2.2.2
  obtain ⟨hab, hnab⟩ := hN11a _ (hc ⊤ hK) TQ (hcomm hVcomm)
  rw [inf_top_eq] at hcardT hcardΩ
  by_cases hTab : IsMulCommutative
      (TQ : Subgroup (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)))
  ·
    left
    have hΩ := CFSG.Goldschmidt.GoldType.omega1_eq_self (hab hTab)
    rw [← hcardT, ← hΩ, hcardΩ, hV]
  ·
    right
    have h4 : Nat.card (Omega1
        (TQ : Subgroup (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)))) ≤ 4 := by
      rw [hcardΩ, hV]
    rw [← hcardT]
    exact sylow_card_of_nonabelian_bender (hnab hTab) TQ h4

end CFSG.GH74.GLS.Th2.P412
