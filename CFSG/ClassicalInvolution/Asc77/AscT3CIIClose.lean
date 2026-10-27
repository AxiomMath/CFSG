module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIExact
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIInv
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexC

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Close

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

@[expose] def LamMem (z a₀ : G) (L : Subgroup G) : Prop :=
  ∃ n ∈ Subgroup.centralizer ({a₀} : Set G), ∃ e : G, IsUniqueInvolution L e ∧ n * e * n⁻¹ = z

omit [Finite G] in
theorem LamMem.of_conj {z a₀ n : G} {L : Subgroup G} (hn : n ∈ Subgroup.centralizer ({a₀} : Set G))
    (h : LamMem z a₀ (conjSub n L)) : LamMem z a₀ L := by
  obtain ⟨n₂, hn₂, e₂, he₂, hne₂⟩ := h
  refine ⟨n₂ * n, (Subgroup.centralizer _).mul_mem hn₂ hn, n⁻¹ * e₂ * n, ?_, ?_⟩
  · have := he₂.conj n⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at this
  · rw [← hne₂]
    group

omit [Finite G] in
theorem LamMem.cent {z a₀ : G} {L : Subgroup G} (h : LamMem z a₀ L)
    (hP : ∀ n ∈ Subgroup.centralizer ({a₀} : Set G), ∀ e : G, IsUniqueInvolution L e →
      n * e * n⁻¹ = z → ∀ l ∈ L, a₀ * (n * l * n⁻¹) = (n * l * n⁻¹) * a₀) :
    ∀ l ∈ L, a₀ * l = l * a₀ := by
  obtain ⟨n, hn, e, he, hne⟩ := h
  intro l hl
  have h2 := hP n hn e he hne l hl
  have h3 : a₀ * n = n * a₀ := (Subgroup.mem_centralizer_singleton_iff.mp hn).symm
  have h4 : a₀ * n⁻¹ = n⁻¹ * a₀ := by
    have := (Subgroup.centralizer ({a₀} : Set G)).inv_mem hn
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  calc a₀ * l = n⁻¹ * (a₀ * (n * l * n⁻¹)) * n := by
        calc a₀ * l = (n⁻¹ * n) * a₀ * l := by group
          _ = n⁻¹ * (n * a₀) * l := by group
          _ = n⁻¹ * (a₀ * n) * l := by rw [h3]
          _ = n⁻¹ * (a₀ * (n * l * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * l * n⁻¹) * a₀) * n := by rw [h2]
    _ = l * a₀ := by
        calc n⁻¹ * ((n * l * n⁻¹) * a₀) * n = l * (n⁻¹ * a₀ * n) := by group
          _ = l * (a₀ * n⁻¹ * n) := by rw [← h4]
          _ = l * a₀ := by group

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem exists_rho {a₀ : G} (haK : K ≤ Subgroup.centralizer ({a₀} : Set G))
    (haJ : J ≤ Subgroup.centralizer ({a₀} : Set G)) :
    ∃ ρ ∈ Subgroup.centralizer ({a₀} : Set G), ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hpair : pairNormalizers K J z t ≤ Subgroup.centralizer ({a₀} : Set G) :=
    sup_le (inf_le_left.trans haK) (inf_le_left.trans haJ)
  refine ⟨t₀ * r, (Subgroup.centralizer _).mul_mem (hpair hh.t₀_mem_pair) (hpair hh.r_mem_pair),
    ?_⟩
  calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
    _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
    _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
    _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
    _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem twinSet_K' : twinSet (CoreAssembly.conjClass K) K' = {K', K} := by
  ext L
  constructor
  · rintro ⟨hL, z', hz'K', hz'L⟩
    have hzz : z' = z := hz'K'.eq d.late_hzK'
    subst hzz
    have hm : L ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hL, z', d.viol.hzK, hz'L⟩
    rw [d.twins] at hm
    rcases hm with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · subst h
      exact ⟨d.late_mem_K', z, d.late_hzK', d.late_hzK'⟩
    · subst h
      exact ⟨d.late_mem_K, z, d.late_hzK', d.viol.hzK⟩

theorem lam_of_adj (hex : ExactMembers (CoreAssembly.conjClass K)) {a₀ : G}
    (hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G)) {ρ : G}
    (hρ : ρ ∈ Subgroup.centralizer ({a₀} : Set G)) (hρt : ρ * t * ρ⁻¹ = z)
    {K₁ K₂ L₂ : Subgroup G} (hK₁ : K₁ ∈ CoreAssembly.conjClass K)
    (hz₁ : IsUniqueInvolution K₁ z) (htw : twinSet (CoreAssembly.conjClass K) K₁ = {K₁, K₂})
    (hsup : K₁ ⊔ K₂ = K ⊔ K') (hadj : aGraphAdj (CoreAssembly.conjClass K) K₁ L₂) :
    LamMem z a₀ L₂ := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hΩ := d.hyp
  obtain ⟨e⟩ := exists_equiv_sl2_of_exact hΩ hex d.late_mem_K
  obtain ⟨e'⟩ := exists_equiv_sl2_of_exact hΩ hex d.late_mem_K'
  have hodd := odd_natCard_galoisField (p := p) (f := f) hp hq
  have hcomm := commute_of_twin_exact hp hq hΩ hex d.late_mem_K d.late_mem_K' d.ne d.viol.hzK
    d.late_hzK'
  have key : ∀ {L₂ : Subgroup G} {t₂ : G},
      AViol (CoreAssembly.conjClass K) K₁ L₂ z t₂ → LamMem z a₀ L₂ := by
    intro L₂ t₂ h
    have ht₂mem : t₂ ∈ K ⊔ K' := hsup ▸ t_mem_sup_of_aviol hp hq hΩ hK₁ h htw
    have ht₂z : t₂ ≠ z := h.ne_involution hΩ hK₁
    obtain ⟨m, hm, hmt⟩ := exists_conj_of_involutions_sup hodd e e' d.viol.hzK d.late_hzK' hcomm
      d.htKK d.viol.hzJ.sq d.viol.hzJ.ne_one d.late_ne_inv ht₂mem h.hzJ.sq h.hzJ.ne_one ht₂z
    have hmc : m⁻¹ ∈ Subgroup.centralizer ({a₀} : Set G) :=
      (Subgroup.centralizer _).inv_mem (hcM hm)
    refine ⟨ρ * m⁻¹, (Subgroup.centralizer _).mul_mem hρ hmc, t₂, h.hzJ, ?_⟩
    calc ρ * m⁻¹ * t₂ * (ρ * m⁻¹)⁻¹ = ρ * (m⁻¹ * (m * t * m⁻¹) * m) * ρ⁻¹ := by rw [hmt]; group
      _ = ρ * t * ρ⁻¹ := by group
      _ = z := hρt
  obtain ⟨hL₂, h | h | ht⟩ := hadj
  · obtain ⟨zK, zJ, hv⟩ := h
    have hzz : zK = z := hv.hzK.eq hz₁
    subst hzz
    exact key hv
  · obtain ⟨zL, zK, hv⟩ := h
    have hzz : zK = z := hv.hzJ.eq hz₁
    subst hzz
    exact key (aviol_symm hp hq hΩ hL₂ hv)
  · obtain ⟨-, z', hz'K, hz'L⟩ := ht.1
    have hzz : z' = z := hz'K.eq hz₁
    subst hzz
    exact ⟨1, Subgroup.one_mem _, z', hz'L, by group⟩

theorem aStar_lam (hex : ExactMembers (CoreAssembly.conjClass K)) {a₀ : G}
    (hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G)) {ρ : G}
    (hρ : ρ ∈ Subgroup.centralizer ({a₀} : Set G)) (hρt : ρ * t * ρ⁻¹ = z) :
    ∀ L, Relation.ReflTransGen (aGraphAdj (CoreAssembly.conjClass K)) K L →
      L ∈ CoreAssembly.conjClass K ∧ LamMem z a₀ L := by
  intro L hL
  induction hL with
  | refl => exact ⟨d.late_mem_K, 1, Subgroup.one_mem _, z, d.viol.hzK, by group⟩
  | @tail L₁ L₂ _ hadj ih =>
    obtain ⟨hL₁, n, hn, e, he, hne⟩ := ih
    have hmem : conjSub n L₁ ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨d.hyp.conjInvariant n L₁ hL₁, z, d.viol.hzK, hne ▸ he.conj n⟩
    have hadj' := aGraphAdj_conj' d.hyp.conjInvariant hadj n
    refine ⟨hadj.1, LamMem.of_conj hn ?_⟩
    rw [d.twins] at hmem
    rcases hmem with h | h
    · rw [h] at hadj'
      exact d.lam_of_adj hex hcM hρ hρt d.late_mem_K d.viol.hzK d.twins rfl hadj'
    · rw [h] at hadj'
      exact d.lam_of_adj hex hcM hρ hρt d.late_mem_K' d.late_hzK' d.twinSet_K' (sup_comm _ _)
        hadj'

theorem exact_cent_false [IsSimpleGroup G] (hex : ExactMembers (CoreAssembly.conjClass K))
    {a₀ : G} (ha1 : a₀ ≠ 1) (haK : ∀ k ∈ K, a₀ * k = k * a₀) (haK' : ∀ k ∈ K', a₀ * k = k * a₀)
    (haJ : ∀ j ∈ J, a₀ * j = j * a₀) : False := by
  have hKc : K ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haK k hk).symm
  have hK'c : K' ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haK' k hk).symm
  have hJc : J ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haJ k hk).symm
  have hcM : K ⊔ K' ≤ Subgroup.centralizer ({a₀} : Set G) := sup_le hKc hK'c
  obtain ⟨ρ, hρ, hρt⟩ := d.exists_rho hKc hJc
  have hΩc := d.hyp.conjInvariant
  have hstar : ∀ L ∈ CoreAssembly.conjClass K, LamMem z a₀ L := fun L hL => by
    have hLs : L ∈ aStar (CoreAssembly.conjClass K) K := by rw [d.star]; exact hL
    exact (d.aStar_lam hex hcM hρ hρt L hLs).2
  have hall : ∀ L ∈ CoreAssembly.conjClass K, ∀ l ∈ L, a₀ * l = l * a₀ := by
    intro L hL
    refine (hstar L hL).cent fun n hn e he hne l hl => ?_
    have hmem : conjSub n L ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨hΩc n L hL, z, d.viol.hzK, hne ▸ he.conj n⟩
    have hl' : n * l * n⁻¹ ∈ conjSub n L := ⟨l, hl, rfl⟩
    rw [d.twins] at hmem
    rcases hmem with h | h
    · rw [h] at hl'
      exact haK _ hl'
    · rw [h] at hl'
      exact haK' _ hl'
  have htop := gen_conjClass K d.viol.hzK.mem d.viol.hzK.ne_one
  have hcent : ∀ g : G, a₀ * g = g * a₀ := by
    intro g
    have hle : (⨆ L ∈ CoreAssembly.conjClass K, L) ≤ Subgroup.centralizer ({a₀} : Set G) :=
      iSup₂_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hall L hL l hl).symm
    have : g ∈ Subgroup.centralizer ({a₀} : Set G) := hle (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hab : ∀ g h : G, g * h = h * g := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exfalso
      apply ha1
      have : a₀ ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hcent g).symm
      rw [h, Subgroup.mem_bot] at this
      exact this
    · intro g h'
      have : g ∈ Subgroup.center G := h ▸ Subgroup.mem_top g
      exact (Subgroup.mem_center_iff.mp this h').symm
  obtain ⟨e⟩ := exists_equiv_sl2_of_exact d.hyp hex d.late_mem_K
  have hq := d.branch.five
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hq
    rw [GaloisField.card p f hf]
    exact (by norm_num : 4 ≤ 5).trans hq
  have := isPerfect_of_equiv_sl2 h4 e
  have : Nontrivial ↥K :=
    ⟨⟨⟨z, d.viol.hzK.mem⟩, 1, fun h => d.viol.hzK.ne_one (congrArg Subtype.val h)⟩⟩
  have : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext (hab a b)⟩⟩
  exact Group.IsPerfect.not_isMulCommutative ↥K inferInstance

end Std20

theorem oddCoreOf_inf_le {L H : Subgroup G} (hHL : H ≤ L) : oddCoreOf L ⊓ H ≤ oddCoreOf H := by
  refine Balance.le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
  · intro g hg
    have hgL : g ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hHL hg))
    have hgM : g ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hg
    rw [mem_normalizer_iff_conjSub_eq] at hgL hgM ⊢
    rw [late_conjSub_inf, hgL, hgM]
  · exact (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem concl20_4_of_hex (hH : Hex20 (CoreAssembly.conjClass K) K J W) :
    Concl20_4 S K K' J z := by
  refine d.concl20_4_of_98 hH ?_ (d.late_tor hH.JW hH.hW)
  exact (d.late_98 hH.JW hH.hW (X := centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (S.isPGroup'.to_le (fun x hx => hx.1)) (fun x hx => hx.1) (fun x hx => d.cent_comm_t hx)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer hx))).2

theorem cent_le_normalizer' {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K' : Set G) := by
  have h1 := mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer ha)
  exact mem_normalizer_iff_conjSub_eq.mpr ((d.late_conj_iff (d.hSz ha.1)).mp h1)

theorem cent_of_mem_A' (hex : ExactMembers (CoreAssembly.conjClass K)) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) :
    (∀ k ∈ K, a * k = k * a) ∧ (∀ k ∈ K', a * k = k * a) ∧ (∀ j ∈ J, a * j = j * a) := by
  have haA : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := ha.1
  have hcomm : ∀ {H : Subgroup G}, H ∈ CoreAssembly.conjClass K → H ≤ K ⊔ K' →
      a ∈ Subgroup.normalizer (H : Set G) → ∀ h ∈ H, a * h = h * a := by
    intro H hH hHM haN h hh
    have h1 : ⁅a, h⁆ ∈ oddCoreOf (K ⊔ K') := haA.2.2.2 h (hHM hh)
    have h2 : ⁅a, h⁆ ∈ H := by
      have e : ⁅a, h⁆ = (a * h * a⁻¹) * h⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp haN h).mp hh) (H.inv_mem hh)
    have h3 := oddCoreOf_inf_le hHM ⟨h1, h2⟩
    rw [oddCoreOf_eq_bot_of_exact hex hH, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  refine ⟨hcomm d.late_mem_K le_sup_left (d.cent_le_normalizer haA),
    hcomm d.late_mem_K' le_sup_right (d.cent_le_normalizer' haA), fun j hj => ?_⟩
  have h1 : ⁅a, j⁆ ∈ oddCoreOf J := ha.2.2.2 j hj
  rw [oddCoreOf_eq_bot_of_exact hex d.late_mem_J, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem concl20_7_of_exact [IsSimpleGroup G] (hex : ExactMembers (CoreAssembly.conjClass K))
    (c4 : Concl20_4 S K K' J z) : Concl20_7 S K K' z := by
  have hA' : centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    by_contra ha1
    obtain ⟨haK, haK', haJ⟩ := d.cent_of_mem_A' hex ha
    exact d.exact_cent_false hex ha1 haK haK' haJ
  show centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z
  rw [c4.1, hA', bot_sup_eq]

end Std20

end Close

end CFSG.ClassicalInvolution.Asc77.T3CII
