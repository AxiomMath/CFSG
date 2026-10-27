module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Action

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_barM {p : ℕ} {M E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (barM M E) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    change (a : ↥M ⧸ CFSG.pCore 2 ↥M) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hcomm.is_comm.comm ⟨(a' : G), Subgroup.mem_subgroupOf.mp ha'⟩
      ⟨(b' : G), Subgroup.mem_subgroupOf.mp hb'⟩
    exact congrArg (Subtype.val : ↥E → G) this
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow]
    have h1 : (x' : G) ^ p = 1 := hexp (x' : G) (Subgroup.mem_subgroupOf.mp hx')
    have h2 : x' ^ p = 1 := Subtype.ext h1
    rw [h2, map_one]

omit [Finite G] in
theorem card_barM_of_faithful {M L P E : Subgroup G} (hEP : E ≤ P) (hPM : P ≤ M)
    (hfaith : P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥) :
    Nat.card (barM M E) = Nat.card E := by
  let g : ↥E →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion (hEP.trans hPM))
  have hrange : g.range = barM M E := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion (hEP.trans hPM) x) = 1 := hx
    have hmem : (x : G) ∈ P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype :=
      ⟨hEP x.2, ⟨Subgroup.inclusion (hEP.trans hPM) x, Subgroup.mem_comap.mpr (by
        rw [hx1]
        exact Subgroup.one_mem _), rfl⟩⟩
    rw [hfaith] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem dvd_card_barM_of_faithful (hOut : KFactOutElemRank) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {M L P : Subgroup G} (hP3 : Open.pRank p P = 3) (hPM : P ≤ M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hLb : IsComponentOf (barM M L) ⊤)
    (hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    (hfaith : P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥) :
    p ∣ Nat.card ↥(barM M L) := by
  by_contra hnd
  obtain ⟨E, hEP, hE, hEcard⟩ := pRank_attained p P (by omega)
  rw [hP3] at hEcard
  have hcard := card_barM_of_faithful (L := L) hEP hPM hfaith
  have hEN : barM M E ≤ Subgroup.normalizer ((barM M L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨m, hm, rfl⟩
    exact mk_mem_normalizer_barM (hPM (hEP (Subgroup.mem_subgroupOf.mp hm)))
      (hPL (hEP (Subgroup.mem_subgroupOf.mp hm)))
  have hEC : barM M E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m, hm, rfl⟩, hmC⟩
    have hmem : (m : G) ∈ P ⊓ ((Subgroup.centralizer (barM M L :
        Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map
        M.subtype := ⟨hEP (Subgroup.mem_subgroupOf.mp hm), ⟨m, hmC, rfl⟩⟩
    rw [hfaith] at hmem
    have : m = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hle := hOut (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (barM M E) hLb hcat p hp hp5 hnd hEN
    (isElemAbelian_barM hE) hEC
  rw [hcard, hEcard] at hle
  have h3 : p ^ 3 ≤ p := hle
  have h1 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at h1
  omega

omit [Finite G] in
theorem card_barM_dvd {M L : Subgroup G} (hLM : L ≤ M) :
    Nat.card ↥(barM M L) ∣ Nat.card ↥L := by
  let f : ↥L →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (barM M L)
      (fun x => ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  exact Subgroup.card_dvd_of_surjective hf

theorem mem_of_dvd_card_of_sylow {p : ℕ} [Fact p.Prime] {P L : Subgroup G} (hP : IsPGroup p P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) {z : G} (hzP : z ∈ P) (hz : orderOf z = p)
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers z)
    (hsyl : ¬ p ∣ ((P ⊓ L).subgroupOf L).index) (hpL : p ∣ Nat.card L) : z ∈ L := by
  have hne : (P ⊓ L).subgroupOf L ≠ ⊥ := by
    intro hbot
    have h := Subgroup.card_mul_index ((P ⊓ L).subgroupOf L)
    have hcard : Nat.card ↥((P ⊓ L).subgroupOf L) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [hcard, one_mul] at h
    exact hsyl (by rw [h]; exact hpL)
  have hnorm : (L.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hPL g.2) (n : G)).mp hn⟩
  have hK : L.subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxP : (x : G) ∈ P := (Subgroup.mem_subgroupOf.mp hx).1
    have : (⟨(x : G), hxP⟩ : ↥P) ∈ L.subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr x.2
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (congrArg (Subtype.val : ↥P → G) this))
  exact Subgroup.mem_subgroupOf.mp (mem_of_normal_ne_bot hP hzP hz huniq hK)

end CFSG.LocalAnalysis.RankThreeTheoremC
