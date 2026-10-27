module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.GH74.Uniqueness.Section15HeringCyclic
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem mem_perfectCore_of_map_simple {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {p : ℕ} {B : Subgroup X} (θ : ↥B →* Y) (hθ : ∀ b, θ b = 1 → p.Coprime (orderOf b))
    {U₀ N : Subgroup X} (hU₀B : U₀ ≤ B) (hU₀N : U₀ ≤ Subgroup.normalizer (N : Set X))
    {K : Subgroup Y} (hK : (U₀.subgroupOf B).map θ = K) (hKs : IsSimpleGroup K)
    (hKp : ⁅K, K⁆ = K) {z : X} (hzU : z ∈ U₀) (hzN : z ∈ N) {k : ℕ} (hzk : z ^ p ^ k = 1)
    (hθz : θ ⟨z, hU₀B hzU⟩ ≠ 1) : z ∈ perfectCore (U₀ ⊓ N) := by
  set W := U₀ ⊓ N with hW
  have hWB : W ≤ B := inf_le_left.trans hU₀B
  set W' := W.subgroupOf B with hW'
  have hW'K : W'.map θ = K := by
    have hle : W'.map θ ≤ K := hK ▸ Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (inf_le_left (a := U₀) (Subgroup.mem_subgroupOf.mp hx))
    have hnorm : ((W'.map θ).subgroupOf K).Normal := by
      constructor
      intro a ha κ
      obtain ⟨b, hbU, hbk⟩ : ∃ b ∈ U₀.subgroupOf B, θ b = (κ : Y) := by
        have hκ : (κ : Y) ∈ (U₀.subgroupOf B).map θ := hK ▸ κ.2
        obtain ⟨b, hb, he⟩ := hκ
        exact ⟨b, hb, he⟩
      have ha' : (a : Y) ∈ W'.map θ := Subgroup.mem_subgroupOf.mp ha
      obtain ⟨w, hw, hwa⟩ := ha'
      have hw' : (w : X) ∈ W := Subgroup.mem_subgroupOf.mp hw
      have hbU' : (b : X) ∈ U₀ := Subgroup.mem_subgroupOf.mp hbU
      refine Subgroup.mem_subgroupOf.mpr ⟨b * w * b⁻¹, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr ⟨U₀.mul_mem (U₀.mul_mem hbU' hw'.1) (U₀.inv_mem hbU'),
          ?_⟩
        have := (Subgroup.mem_normalizer_iff.mp (hU₀N hbU') (w : X)).mp hw'.2
        simpa using this
      · simp only [map_mul, map_inv, hbk, hwa, Subgroup.coe_mul, Subgroup.coe_inv]
    have hne : (W'.map θ).subgroupOf K ≠ ⊥ := by
      intro hbot
      apply hθz
      have hzW : (⟨z, hU₀B hzU⟩ : B) ∈ W' := Subgroup.mem_subgroupOf.mpr ⟨hzU, hzN⟩
      have hmem : θ ⟨z, hU₀B hzU⟩ ∈ W'.map θ := ⟨_, hzW, rfl⟩
      have hK' : θ ⟨z, hU₀B hzU⟩ ∈ K := hle hmem
      have : (⟨θ ⟨z, hU₀B hzU⟩, hK'⟩ : K) ∈ (W'.map θ).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hmem
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((W'.map θ).subgroupOf K) with h1 | h1
    · exact absurd h1 hne
    · refine le_antisymm hle fun y hy => ?_
      have : (⟨y, hy⟩ : K) ∈ (W'.map θ).subgroupOf K := h1 ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hcore : (perfectCore W').map θ = K := by
    rw [map_perfectCore, hW'K, perfectCore_eq_self_of_perfect hKp]
  have hzK : θ ⟨z, hU₀B hzU⟩ ∈ K := by
    rw [← hW'K]; exact ⟨_, Subgroup.mem_subgroupOf.mpr ⟨hzU, hzN⟩, rfl⟩
  rw [← hcore] at hzK
  obtain ⟨v, hv, hvz⟩ := hzK
  have hPW : (perfectCore W').map B.subtype = perfectCore W := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hWB]
  have hvW : (v : X) ∈ perfectCore W := hPW ▸ ⟨v, hv, rfl⟩
  have hvW' : (v : X) ∈ W := perfectCore_le W hvW
  have hzW : z ∈ W := ⟨hzU, hzN⟩
  set n : B := v⁻¹ * ⟨z, hU₀B hzU⟩ with hn
  have hn1 : θ n = 1 := by rw [hn, map_mul, map_inv, hvz, inv_mul_cancel]
  have hnc := hθ n hn1
  have hNorm := perfectCore_normal W
  set q := QuotientGroup.mk' ((perfectCore W).subgroupOf W)
  have hqv : q ⟨v, hvW'⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.mem_subgroupOf.mpr hvW)
  have hnW : (n : X) ∈ W := W.mul_mem (W.inv_mem hvW') hzW
  have hqz : q ⟨z, hzW⟩ = q ⟨n, hnW⟩ := by
    have e : (⟨z, hzW⟩ : W) = ⟨v, hvW'⟩ * ⟨n, hnW⟩ := by
      apply Subtype.ext
      simp [hn]
    rw [e, map_mul, hqv, one_mul]
  have h1 : orderOf (q ⟨z, hzW⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨z, hzW⟩ : W) ^ p ^ k = 1 := Subtype.ext (by simpa using hzk)
    rw [this, map_one]
  have h2 : orderOf (q ⟨z, hzW⟩) ∣ orderOf n := by
    rw [hqz]
    refine (orderOf_map_dvd q _).trans ?_
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have h3 : orderOf (q ⟨z, hzW⟩) = 1 := by
    have hc : (p ^ k).Coprime (orderOf n) := Nat.Coprime.pow_left k hnc
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
  have h4 : (⟨z, hzW⟩ : W) ∈ (perfectCore W).subgroupOf W :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact Subgroup.mem_subgroupOf.mp h4

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem exists_perfect_cover_onto (hp : p.Prime)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) {z : G} (hzH : z ∈ H) (hzM : z ∈ M) (hzo : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L₂) :
    ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U ∧
      (∀ u ∈ U, ∀ huH : u ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨u, huH⟩ ∈ L₂) ∧
      ∀ l ∈ L₂, ∃ u ∈ U, ∃ huH : u ∈ H,
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨u, huH⟩ = l := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set Y : Subgroup G := (L₂.comap π).map H.subtype ⊓ M
  have hYHM : Y ≤ H ⊓ M := le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) inf_le_right
  have hYH : Y ≤ H := hYHM.trans inf_le_left
  set U := perfectCore Y
  have hUY : U ≤ Y := perfectCore_le Y
  set ψ := π.comp (Subgroup.inclusion hYH)
  have hzY : z ∈ Y := ⟨⟨⟨z, hzH⟩, hzL, rfl⟩, hzM⟩
  have hrange : ψ.range = L₂ := by
    refine le_antisymm ?_ fun l hl => ?_
    · rintro _ ⟨⟨y, ⟨h, hh, rfl⟩, -⟩, rfl⟩
      have : Subgroup.inclusion hYH ⟨(h : G), ⟨h, hh, rfl⟩, ‹_›⟩ = h := Subtype.ext rfl
      simpa [ψ, this] using hh
    · obtain ⟨h, hh, rfl⟩ := hL₂X hl
      have hhM : (h : G) ∈ M := (Subgroup.mem_subgroupOf.mp hh).2
      refine ⟨⟨h, ⟨h, ?_, rfl⟩, hhM⟩, ?_⟩
      · exact hl
      · show π (Subgroup.inclusion hYH _) = π h
        congr 1
  have hW : (perfectCore (⊤ : Subgroup ↥Y)).map ψ = L₂ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hrange]
    exact perfectCore_eq_self_of_perfect (commutator_eq_self_of_component hL₂)
  have hWU : (perfectCore (⊤ : Subgroup ↥Y)).map Y.subtype = U := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzU : z ∈ U := by
    have hzW : π ⟨z, hzH⟩ ∈ (perfectCore (⊤ : Subgroup ↥Y)).map ψ := by
      rw [hW]
      exact hzL
    obtain ⟨w', hw'W, hw'z⟩ := hzW
    have hwU : (w' : G) ∈ U := hWU ▸ ⟨w', hw'W, rfl⟩
    set n : ↥Y := w'⁻¹ * ⟨z, hzY⟩
    have hn : p.Coprime (orderOf n) := by
      have h1 : ψ n = 1 := by
        rw [map_mul, map_inv, hw'z]
        exact inv_mul_cancel _
      have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
      have h3 : orderOf (Subgroup.inclusion hYH n) ∣ Nat.card (GLBPrimeCore p H) := by
        have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H)
          (x := (Subgroup.inclusion hYH n : G)) h2
        rwa [Subgroup.orderOf_coe] at this
      rw [orderOf_injective _ (Subgroup.inclusion_injective hYH)] at h3
      exact (glbPrimeCore_coprime p H).coprime_dvd_right h3
    have hUn : (U.subgroupOf Y).Normal := perfectCore_normal Y
    set q := QuotientGroup.mk' (U.subgroupOf Y)
    have hqw : q w' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwU)
    have hqz : q ⟨z, hzY⟩ = q n := by
      rw [show n = w'⁻¹ * ⟨z, hzY⟩ from rfl, map_mul, map_inv, hqw, inv_one, one_mul]
    have hzp : orderOf (⟨z, hzY⟩ : ↥Y) = p := by rw [Subgroup.orderOf_mk]; exact hzo
    have h1 : orderOf (q ⟨z, hzY⟩) ∣ p := hzp ▸ orderOf_map_dvd q _
    have h2 : orderOf (q ⟨z, hzY⟩) ∣ orderOf n := hqz ▸ orderOf_map_dvd q n
    have h3 : orderOf (q ⟨z, hzY⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hn) h2
    have h4 : ⟨z, hzY⟩ ∈ U.subgroupOf Y :=
      (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
    exact Subgroup.mem_subgroupOf.mp h4
  refine ⟨U, hUY.trans hYHM, perfectCore_perfect Y, hzU, ?_, ?_⟩
  · intro u hu huH
    obtain ⟨⟨h, hh, he⟩, -⟩ := hUY hu
    have : h = ⟨u, huH⟩ := Subtype.ext he
    rw [← this]
    exact hh
  · intro l hl
    rw [← hW] at hl
    obtain ⟨w', hw'W, hw'l⟩ := hl
    exact ⟨w', hWU ▸ ⟨w', hw'W, rfl⟩, hYH w'.2, hw'l⟩

theorem catalogSimpleSections_of_isKGroup {X : Type*} [Group X] (hX : Open.IsKGroup X) :
    CatalogSimpleSections X := by
  intro K L hL hs hn
  have e : (L.map K.subtype).subgroupOf K = L :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective L
  revert hL hs hn
  rw [← e]
  intro hL hs hn
  exact hX K (L.map K.subtype) (Subgroup.map_subtype_le L) hs hn

theorem D1PhaseThree.mem_sup_of_perfect_cat (h : D1PhaseThree p P M H R)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hVp : ⁅V, V⁆ = V)
    (hVL : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {u : ↥M ⧸ CFSG.pCore 2 ↥M} (huV : u ∈ V) :
    u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  perfect_le_sup_centralizer_of_outer (isSolvable_outer_of_component hSch hL.component
    (((catalogSimpleSections_of_isKGroup h.isKGroup.1).quotient
      (CFSG.pCore 2 ↥M)).isCatalogGroup_center_quotient hL.component)) hVp hVL huV

omit [Finite G] in
theorem conj_mem_iInf_normalizer_barM {g : G} (hgM : g ∈ M) (hgH : g ∈ H)
    {n : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hn : n ∈ ⨅ L : {L : Subgroup G // IsWeakSBlock M (pCoreOf 2 H) L},
      Subgroup.normalizer (barM M L.1 : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    mbar M g hgM * n * (mbar M g hgM)⁻¹ ∈ ⨅ L : {L : Subgroup G // IsWeakSBlock M (pCoreOf 2 H) L},
      Subgroup.normalizer (barM M L.1 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [Subgroup.mem_iInf]
  rintro ⟨L, hL⟩
  have hL' : IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hL.map_conj (M.inv_mem hgM) (localGroup_le_normalizer_pCoreOf 2 H (H.inv_mem hgH))
  have hnL' := (Subgroup.mem_iInf.mp hn) ⟨_, hL'⟩
  change n ∈ Subgroup.normalizer
    (barM M (L.map (MulAut.conj g⁻¹).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) at hnL'
  rw [barM_map_conj (M.inv_mem hgM) L] at hnL'
  set u := mbar M g hgM with hu
  have hu' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g⁻¹, M.inv_mem hgM⟩ = u⁻¹ := by
    rw [hu, ← mbar_inv hgM]
  rw [hu'] at hnL'
  have key : ∀ y, y ∈ (barM M L).map (MulAut.conj u⁻¹).toMonoidHom ↔
      u * y * u⁻¹ ∈ barM M L := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [mul_assoc] using hx
    · intro hy
      refine ⟨u * y * u⁻¹, hy, ?_⟩
      simp [mul_assoc]
  rw [Subgroup.mem_normalizer_iff] at hnL' ⊢
  intro x
  have h1 := key (u⁻¹ * x * u)
  have h2 := hnL' (u⁻¹ * x * u)
  have h3 := key (n * (u⁻¹ * x * u) * n⁻¹)
  have e1 : u * (u⁻¹ * x * u) * u⁻¹ = x := by group
  have e2 : u * (n * (u⁻¹ * x * u) * n⁻¹) * u⁻¹ = u * n * u⁻¹ * x * (u * n * u⁻¹)⁻¹ := by group
  rw [e1] at h1
  rw [e2] at h3
  exact h1.symm.trans (h2.trans h3)

theorem D1CaseTwoDataAt.exists_perfect_blocks (hd : D1CaseTwoDataAt p P M H R Rbar)
    (h : D1PhaseThree p P M H R)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) {z : G} (hzH : z ∈ H) (hzM : z ∈ M) (hzo : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L₂)
    (hzN : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      mbar M z hzM ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧ V ≤ barM M (H ⊓ M) ∧
      mbar M z hzM ∈ V ∧ ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hUHM, -, hzU, hUL, honto⟩ := exists_perfect_cover_onto hp hL₂ hL₂X hzH hzM hzo hzL
  set B := barM M (H ⊓ M) with hB
  obtain ⟨θ, hθk, hθ⟩ := exists_barM_hom_of h
  have hθk' : ∀ y, θ y = 1 → p.Coprime (orderOf y) := fun y hy =>
    hθk.coprime_dvd_right (Subgroup.orderOf_dvd_natCard θ.ker (x := y) hy)
  set U₀ := barM M U with hU₀
  have hU₀B : U₀ ≤ B := barM_mono hUHM
  set N₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    ⨅ L : {L : Subgroup G // IsWeakSBlock M (pCoreOf 2 H) L},
      Subgroup.normalizer (barM M L.1 : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hN₀
  have hU₀N : U₀ ≤ Subgroup.normalizer (N₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    have hgH := (hUHM (Subgroup.mem_subgroupOf.mp hg)).1
    exact CFSG.GH74.Uniqueness.Hering.mem_normalizer_of_conj_mem fun n hn =>
      conj_mem_iInf_normalizer_barM hgM hgH hn
  have hK : (U₀.subgroupOf B).map θ = L₂ := by
    refine le_antisymm ?_ fun l hl => ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_subgroupOf.mp hx
      have hmU : (m : G) ∈ U := Subgroup.mem_subgroupOf.mp hm
      have hmH : (m : G) ∈ H := (hUHM hmU).1
      have hmB : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ B := hmx ▸ x.2
      have hx' : x = ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmB⟩ := Subtype.ext hmx.symm
      rw [hx', hθ m hmH]
      exact hUL m hmU hmH
    · obtain ⟨u, huU, huH, hul⟩ := honto l hl
      have huM : u ∈ M := (hUHM huU).2
      have hmB : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, huM⟩ ∈ B :=
        ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr (hUHM huU), rfl⟩
      refine ⟨⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, huM⟩, hmB⟩,
        Subgroup.mem_subgroupOf.mpr ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr huU, rfl⟩, ?_⟩
      rw [hθ ⟨u, huM⟩ huH]
      exact hul
  obtain ⟨hsimple, -, -, -⟩ := hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL₂
    (hd.cyclic L₂ hL₂)
  have hKp := commutator_eq_self_of_component hL₂
  have hzU₀ : mbar M z hzM ∈ U₀ := ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzU, rfl⟩
  have hzN₀ : mbar M z hzM ∈ N₀ := Subgroup.mem_iInf.mpr fun L => hzN L.1 L.2
  have hzk : (mbar M z hzM) ^ p ^ 1 = 1 := by
    rw [pow_one, ← mbar_pow, ← mbar_one]
    congr 1
    rw [← hzo]
    exact pow_orderOf_eq_one z
  have hθz : θ ⟨mbar M z hzM, hU₀B hzU₀⟩ ≠ 1 := by
    have e := hθ ⟨z, hzM⟩ hzH (hU₀B hzU₀)
    change θ ⟨mbar M z hzM, hU₀B hzU₀⟩ = _ at e
    rw [e]
    intro h1
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 : orderOf z ∣ Nat.card (GLBPrimeCore p H) := Subgroup.orderOf_dvd_natCard _ h2
    rw [hzo] at h3
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime p H) h3)
  have hNL : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      N₀ ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    iInf_le (fun L : {L : Subgroup G // IsWeakSBlock M (pCoreOf 2 H) L} =>
      Subgroup.normalizer (barM M L.1 : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ⟨L, hL⟩
  clear_value N₀ U₀
  have hmem := mem_perfectCore_of_map_simple (K := L₂) (N := N₀) θ hθk' hU₀B hU₀N hK hsimple
    hKp hzU₀ hzN₀ hzk hθz
  refine ⟨perfectCore (U₀ ⊓ N₀), perfectCore_perfect _,
    (perfectCore_le _).trans (inf_le_left.trans hU₀B), hmem, fun L hL => ?_⟩
  exact (perfectCore_le _).trans (inf_le_right.trans (hNL L hL))

theorem D1CaseTwoData.exists_perfect_blocks (hd : D1CaseTwoData p P M H R Rbar)
    (h : D1PhaseThree p P M H R)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) {z : G} (hzH : z ∈ H) (hzM : z ∈ M) (hzo : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L₂)
    (hzN : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      mbar M z hzM ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧ V ≤ barM M (H ⊓ M) ∧
      mbar M z hzM ∈ V ∧ ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  D1CaseTwoDataAt.exists_perfect_blocks (hd := hd.toAt) (h := h) (hL₂ := hL₂) (hL₂X := hL₂X)
    (hzH := hzH) (hzM := hzM) (hzo := hzo) (hzL := hzL) (hzN := hzN)

end CFSG.AGLEmbedding
