module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264D
public import CFSG.ClassicalInvolution.Q3.TL4E4CoverNbrs
public import Certificates.Certificate55120
public import CFSG.ClassicalInvolution.Q3.TL4Conn264T

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E4Cover

variable {X : Type} [Group X] [Finite X] {K : Subgroup X} {u : X}

theorem conjSub_inf_eq_bot {N : Subgroup X} [N.Normal] (hN2 : IsPGroup 2 ↥N)
    (hu : IsUniqueInvolution K u) (huN : u ∉ N) (g : X) : conjSub g K ⊓ N = ⊥ := by
  by_contra hne
  have hnt : Nontrivial ↥(conjSub g K ⊓ N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have h2 : IsPGroup 2 ↥(conjSub g K ⊓ N) := hN2.to_le inf_le_right
  have hdvd : 2 ∣ Nat.card ↥(conjSub g K ⊓ N) := by
    rcases h2.card_eq_or_dvd with h1 | h1
    · exact absurd h1 Finite.one_lt_card.ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : (x : X) * x = 1 := by
    have h3 := pow_orderOf_eq_one x
    rw [hx, sq] at h3
    exact congrArg Subtype.val h3
  have hx1 : (x : X) ≠ 1 := fun h => by
    have h4 : x = 1 := Subtype.ext h
    rw [h4, orderOf_one] at hx
    norm_num at hx
  have h5 := ((hu.conj g).unique _ x.2.1 hx2).resolve_left hx1
  have h6 : g * u * g⁻¹ ∈ N := h5 ▸ x.2.2
  apply huN
  have h7 := (inferInstance : N.Normal).conj_mem _ h6 g⁻¹
  simpa [mul_assoc] using h7

theorem le_center_of_meet (h : TypeRFam 3 (CoreAssembly.conjClass K))
    (hgen : (⨆ g : X, conjSub g K) = ⊤) {N : Subgroup X} [N.Normal] (hN2 : IsPGroup 2 ↥N)
    (hmeet : ∀ g : X, conjSub g K ⊓ N = ⊥) : N ≤ Subgroup.center X := by
  have hL : ∀ g : X, conjSub g K ≤ Subgroup.centralizer (N : Set X) := by
    intro g
    have hLΦ : conjSub g K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
    rw [← h.closure_twoElts hLΦ, Subgroup.closure_le]
    rintro x ⟨hxL, hx2⟩
    have hH : IsPGroup 2 ↥((Subgroup.zpowers x).comap (conjSub g K).subtype) :=
      hx2.comap_of_injective _ Subtype.val_injective
    obtain ⟨P, hP⟩ := hH.exists_le_sylow
    set R : Subgroup X := (P : Subgroup ↥(conjSub g K)).map (conjSub g K).subtype with hRdef
    have hR : R ∈ RSet (CoreAssembly.conjClass K) := ⟨conjSub g K, hLΦ, P, rfl⟩
    have hRN : R ⊓ N = ⊥ := by
      rw [eq_bot_iff, ← hmeet g]
      exact inf_le_inf_right _ (Subgroup.map_subtype_le _)
    have hc := comm613Gen_normal h.hyp hR inferInstance hRN
    rw [PhilipHall.Frame.oddCoreOf_eq_bot_of_isPGroup hN2, le_bot_iff] at hc
    have hRC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    exact hRC ⟨⟨x, hxL⟩, hP (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers x)), rfl⟩
  have hX : (⊤ : Subgroup X) ≤ Subgroup.centralizer (N : Set X) := by
    rw [← hgen]
    exact iSup_le hL
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_centralizer_iff.mp (hX (Subgroup.mem_top y)) n hn).symm

theorem center_eq_bot_of_simple {M : Type} [Group M] [IsSimpleGroup M]
    (hnab : ∃ a b : M, a * b ≠ b * a) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h1 | h1
  · exact h1
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center M := h1 ▸ Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

theorem twinE4_center (h : TypeRFam 3 (CoreAssembly.conjClass K))
    (hgen : (⨆ g : X, conjSub g K) = ⊤) (hO : classicalInvolutionOddCore X = ⊥)
    (hu : IsUniqueInvolution K u) (hu2 : ¬ ∃ P : Subgroup X, P.Normal ∧ IsPGroup 2 ↥P ∧ u ∈ P)
    (hE : PhilipHall.Frame.TwinE4 X) :
    IsPGroup 2 ↥(Subgroup.center X) ∧ u ∉ Subgroup.center X ∧
      PhilipHall.QuaternionBridge.ExLie (X ⧸ Subgroup.center X) ∧
        Nonempty (↥K ≃* QuaternionGroup 2) := by
  obtain ⟨Q, _, f, hfs, hk2, hQ⟩ := hE
  have : Finite Q := Finite.of_surjective f hfs
  have huk : u ∉ f.ker := fun h' => hu2 ⟨f.ker, inferInstance, hk2, h'⟩
  have hkc : f.ker ≤ Subgroup.center X :=
    le_center_of_meet h hgen hk2 (fun g => conjSub_inf_eq_bot hk2 hu huk g)
  have hK := CoreAssembly.mem_conjClass_self K
  have hKk : K ⊓ f.ker = ⊥ := by simpa using conjSub_inf_eq_bot hk2 hu huk 1
  have hnabK : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
    obtain ⟨-, P, hP, hnc⟩ := h.hyp.omega1 K hK
    by_contra hall
    push Not at hall
    exact hnc ⟨⟨fun a b => Subtype.ext (hall a (hP.1 a.2) b (hP.1 b.2))⟩⟩
  have hnabQ : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnabK
    refine ⟨f a, f b, fun e => hab ?_⟩
    have hm : a * b * (b * a)⁻¹ ∈ K ⊓ f.ker := by
      refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem ha hb) (K.inv_mem (K.mul_mem hb ha)), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, e, mul_inv_cancel]
    rw [hKk, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  have hs : IsSimpleGroup Q := Vtx.isSimpleGroup_of_exLie hQ
  have hZQ : Subgroup.center Q = ⊥ := center_eq_bot_of_simple hnabQ
  have hck : Subgroup.center X ≤ f.ker := by
    intro c hc
    have hfc : f c ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hfs q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc y]
    rw [hZQ, Subgroup.mem_bot] at hfc
    exact hfc
  have hkZ : f.ker = Subgroup.center X := le_antisymm hkc hck
  have hZ2 : IsPGroup 2 ↥(Subgroup.center X) := hkZ ▸ hk2
  have huZ : u ∉ Subgroup.center X := hkZ ▸ huk
  have e : X ⧸ Subgroup.center X ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hkZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hM : PhilipHall.QuaternionBridge.ExLie (X ⧸ Subgroup.center X) := by
    rcases hQ with hQ | hQ
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hQ)
  have hsM : IsSimpleGroup (X ⧸ Subgroup.center X) := Vtx.isSimpleGroup_of_exLie hM
  have hZM := Vtx.center_quot_center_eq_bot hsM
  have ht : orderOf (QuotientGroup.mk u : X ⧸ Subgroup.center X) = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← QuotientGroup.mk_mul, hu.sq, QuotientGroup.mk_one]
    · intro h1
      exact huZ ((QuotientGroup.eq_one_iff u).mp h1)
  have hle := Vtx.oddCent_le_center_of_mk (Vtx.oddCoreIn_centralizer_eq_bot_of_exLie hM hZM ht)
  have hnormal : (oddCoreImg (Subgroup.centralizer ({u} : Set X))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_center_iff.mp (hle hx) g, mul_inv_cancel_right]
      exact hx⟩
  have hθ : oddCoreImg (Subgroup.centralizer ({u} : Set X)) = ⊥ := by
    have hO' : oddCoreImg (Subgroup.centralizer ({u} : Set X)) ≤ classicalInvolutionOddCore X :=
      le_sSup ⟨hnormal, odd_natCard_oddCoreImg _⟩
    rw [hO] at hO'
    exact le_bot_iff.mp hO'
  have hK2 : IsPGroup 2 ↥K :=
    PhilipHall.Frame.isPGroup_of_oddCent h.hyp hK hu hθ (h.twoGroup K hK)
  exact ⟨hZ2, huZ, hM, h.quat K hK K (Vtx.isSylow2In_self hK2)⟩

omit [Finite X] in
theorem zpowers_le_normalizer_of_mul_comm {M : Type} [Group M] {a b : M} (h : a * b = b * a) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set M) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact Commute.zpow_left (Commute.symm h) k

theorem exists_three_of_mk {N : Subgroup X} [N.Normal] (hN2 : IsPGroup 2 ↥N)
    (hK2 : IsPGroup 2 ↥K) {g₁ g₂ : X} {v₀ v₁ v₂ : X ⧸ N}
    (h0 : v₀ ∈ K.map (QuotientGroup.mk' N)) (h1 : v₁ ∈ (conjSub g₁ K).map (QuotientGroup.mk' N))
    (h2 : v₂ ∈ (conjSub g₂ K).map (QuotientGroup.mk' N))
    (c01 : v₀ * v₁ = v₁ * v₀) (c02 : v₀ * v₂ = v₂ * v₀) (c12 : v₁ * v₂ = v₂ * v₁)
    (o0 : v₀ ^ 2 ≠ 1) (o1 : v₁ ^ 2 ≠ 1) (o2 : v₂ ^ 2 ≠ 1)
    (d1 : (conjSub g₁ K).map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N))
    (d2 : (conjSub g₂ K).map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N))
    (d12 : (conjSub g₁ K).map (QuotientGroup.mk' N) ≠ (conjSub g₂ K).map (QuotientGroup.mk' N)) :
    ∃ K₁ ∈ CoreAssembly.conjClass K, ∃ K₂ ∈ CoreAssembly.conjClass K, ∃ P : Subgroup X,
      IsPGroup 2 ↥P ∧ K₁ ≠ K ∧ K₂ ≠ K ∧ K₁ ≠ K₂ ∧ 2 < Nat.card ↥(K ⊓ P) ∧
        2 < Nat.card ↥(K₁ ⊓ P) ∧ 2 < Nat.card ↥(K₂ ⊓ P) := by
  have hc2 : ∀ g : X, IsPGroup 2 ↥(conjSub g K) := fun g => hK2.map _
  have hz : ∀ (L : Subgroup X) (v : X ⧸ N), IsPGroup 2 ↥L → v ∈ L.map (QuotientGroup.mk' N) →
      IsPGroup 2 ↥(Subgroup.zpowers v) :=
    fun L v hL hv => (hL.map _).to_le (Subgroup.zpowers_le.mpr hv)
  set Pb : Subgroup (X ⧸ N) :=
    Subgroup.zpowers v₀ ⊔ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ with hPbdef
  have hPb : IsPGroup 2 ↥Pb :=
    ((hz K v₀ hK2 h0).to_sup_of_normal_right' (hz _ v₁ (hc2 g₁) h1)
      (zpowers_le_normalizer_of_mul_comm c01)).to_sup_of_normal_right'
      (hz _ v₂ (hc2 g₂) h2)
      (sup_le (zpowers_le_normalizer_of_mul_comm c02) (zpowers_le_normalizer_of_mul_comm c12))
  set P : Subgroup X := Pb.comap (QuotientGroup.mk' N) with hPdef
  have hP : IsPGroup 2 ↥P :=
    hPb.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
  have hcard : ∀ (L : Subgroup X) (v : X ⧸ N), v ∈ L.map (QuotientGroup.mk' N) → v ∈ Pb →
      v ^ 2 ≠ 1 → 2 < Nat.card ↥(L ⊓ P) := by
    rintro L _ ⟨w, hw, rfl⟩ hvP hv2
    have hle : Subgroup.zpowers w ≤ L ⊓ P := Subgroup.zpowers_le.mpr ⟨hw, hvP⟩
    have hw2 : 2 < orderOf w := by
      by_contra hle2
      apply hv2
      have hw1 : w ^ 2 = 1 := by
        rcases (by have := orderOf_pos w; omega : orderOf w = 1 ∨ orderOf w = 2) with h | h
        · rw [orderOf_eq_one_iff.mp h, one_pow]
        · rw [← h]
          exact pow_orderOf_eq_one w
      rw [← map_pow, hw1, map_one]
    calc 2 < orderOf w := hw2
      _ = Nat.card ↥(Subgroup.zpowers w) := (Nat.card_zpowers w).symm
      _ ≤ Nat.card ↥(L ⊓ P) := Subgroup.card_le_of_le hle
  refine ⟨conjSub g₁ K, ⟨g₁, rfl⟩, conjSub g₂ K, ⟨g₂, rfl⟩, P, hP, fun h => d1 (by rw [h]),
    fun h => d2 (by rw [h]), fun h => d12 (by rw [h]), hcard K v₀ h0 ?_ o0,
    hcard _ v₁ h1 ?_ o1, hcard _ v₂ h2 ?_ o2⟩
  · exact (le_sup_left.trans le_sup_left : Subgroup.zpowers v₀ ≤ Pb) (Subgroup.mem_zpowers v₀)
  · exact (le_sup_right.trans le_sup_left : Subgroup.zpowers v₁ ≤ Pb) (Subgroup.mem_zpowers v₁)
  · exact (le_sup_right : Subgroup.zpowers v₂ ≤ Pb) (Subgroup.mem_zpowers v₂)

end E4Cover

namespace E4Sp6

theorem sp6_three_parts : rho () * uOne () = uOne () * rho () ∧
    rho () * uTwo () = uTwo () * rho () ∧ uOne () * uTwo () = uTwo () * uOne () ∧
    rho () ^ 2 ≠ 1 ∧ uOne () ^ 2 ≠ 1 ∧ uTwo () ^ 2 ≠ 1 ∧ uTwo () ∉ L0 () ∧
    (twin ())⁻¹ * uTwo () * twin () ∉ L0 () := by
  have h : sp6ThreeCheck () = true := Certificates.certificate55120
  simp only [sp6ThreeCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end E4Sp6

namespace E4Cover

theorem sp6_three {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1)
    {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    ∃ m₁ m₂ : M, ∃ v₀ ∈ K, ∃ v₁ ∈ conjSub m₁ K, ∃ v₂ ∈ conjSub m₂ K,
      v₀ * v₁ = v₁ * v₀ ∧ v₀ * v₂ = v₂ * v₀ ∧ v₁ * v₂ = v₂ * v₁ ∧ v₀ ^ 2 ≠ 1 ∧ v₁ ^ 2 ≠ 1 ∧
        v₂ ^ 2 ≠ 1 ∧ conjSub m₁ K ≠ K ∧ conjSub m₂ K ≠ K ∧ conjSub m₁ K ≠ conjSub m₂ K := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKc⟩ := E4Sp6.exists_emb e hd
  have hpre : ∀ g ∈ CFSG.Sporadic.Schreier.Co3.co3X36, ∃ m : M, φ m = g :=
    fun g hg => MonoidHom.mem_range.mp (hrange ▸ hg)
  obtain ⟨m₁, hm₁⟩ : ∃ m : M, φ m = E4Sp6.twin () := hpre _ (E4Sp6.ws_mem 11)
  obtain ⟨m₂, hm₂⟩ : ∃ m : M, φ m = E4Sp6.wOne () := hpre _ (E4Sp6.ws_mem 1)
  have hρ : E4Sp6.rho () ∈ K.map φ := hKc ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : E4Sp6.jay () ∈ K.map φ :=
    hKc ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨k₀, hk₀, hφ₀⟩ := hρ
  obtain ⟨k₁, hk₁, hφ₁⟩ := hj
  obtain ⟨c01, c02, c12, o0, o1, o2, n0, n1⟩ := E4Sp6.sp6_three_parts
  obtain ⟨v₁, hv₁def⟩ : ∃ v : M, v = m₁ * (k₀ * k₁) * m₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂def⟩ : ∃ v : M, v = m₂ * k₀ * m₂⁻¹ := ⟨_, rfl⟩
  have hφv₁ : φ v₁ = E4Sp6.uOne () := by
    unfold E4Sp6.uOne
    rw [hv₁def, map_mul, map_mul, map_inv, map_mul, hφ₀, hφ₁, hm₁]
  have hφv₂ : φ v₂ = E4Sp6.uTwo () := by
    unfold E4Sp6.uTwo
    rw [hv₂def, map_mul, map_mul, map_inv, hφ₀, hm₂]
  have hmap : ∀ m : M, (conjSub m K).map φ = conjSub (φ m) E4Sp6.K0 := fun m => by
    rw [← conjSub_map, hKc]
  have hv₁ : v₁ ∈ conjSub m₁ K := hv₁def ▸ conj_mem_conjSub (K.mul_mem hk₀ hk₁) m₁
  have hv₂ : v₂ ∈ conjSub m₂ K := hv₂def ▸ conj_mem_conjSub hk₀ m₂
  refine ⟨m₁, m₂, k₀, hk₀, v₁, hv₁, v₂, hv₂,
    hφ (by rw [map_mul, map_mul, hφ₀, hφv₁]; exact c01),
    hφ (by rw [map_mul, map_mul, hφ₀, hφv₂]; exact c02),
    hφ (by rw [map_mul, map_mul, hφv₁, hφv₂]; exact c12),
    fun h => o0 (by rw [← hφ₀, ← map_pow, h, map_one]),
    fun h => o1 (by rw [← hφv₁, ← map_pow, h, map_one]),
    fun h => o2 (by rw [← hφv₂, ← map_pow, h, map_one]), ?_, ?_, ?_⟩
  · intro h
    apply E4Sp6.edge.1
    rw [← hm₁, ← hmap, h, hKc]
  · intro h
    apply n0
    have hmem : E4Sp6.uTwo () ∈ E4Sp6.K0 := by
      rw [← hφv₂, ← hKc, ← h]
      exact Subgroup.mem_map_of_mem φ hv₂
    exact (E4Sp6.mem_K0_iff _).mp hmem
  · intro h
    apply n1
    have hmem : E4Sp6.uTwo () ∈ conjSub (E4Sp6.twin ()) E4Sp6.K0 := by
      rw [← hφv₂, ← hm₁, ← hmap, h]
      exact Subgroup.mem_map_of_mem φ hv₂
    exact (E4Sp6.mem_K0_iff _).mp (mem_conjSub_iff.mp hmem)

end E4Cover

theorem e4CoverThree_proved :
    ∀ (X : Type) [Group X] [Finite X] (N : Subgroup X) [N.Normal] (K : Subgroup X) (u : X),
      IsPGroup 2 ↥N → N ≤ Subgroup.center X → HypOmegaGen (CoreAssembly.conjClass K) →
      Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K u → u ∉ N →
      (∀ L ∈ twinSet (CoreAssembly.conjClass K) K, L = K) →
      PhilipHall.QuaternionBridge.ExLie (X ⧸ N) →
        ∃ K₁ ∈ CoreAssembly.conjClass K, ∃ K₂ ∈ CoreAssembly.conjClass K, ∃ P : Subgroup X,
          IsPGroup 2 ↥P ∧ K₁ ≠ K ∧ K₂ ≠ K ∧ K₁ ≠ K₂ ∧ 2 < Nat.card ↥(K ⊓ P) ∧
            2 < Nat.card ↥(K₁ ⊓ P) ∧ 2 < Nat.card ↥(K₂ ⊓ P) := by
  intro X _ _ N _ K u hN2 hNc hΩ hq hu huN htw hM
  have hd := E4Cover.quatTwinDatum_mk hNc hΩ hq hu huN htw
  have hK2 := E4Cover.isPGroup_of_mem_conjClass hq K (CoreAssembly.mem_conjClass_self K)
  have h2 := E4Cover.isPGroup_of_mem_conjClass hq
  have c := PhilipHall.Frame.TwinDisc.ExitE4.centQuotGen hΩ h2 hNc
    (E4Cover.inf_eq_bot_of_mem_conjClass hq hΩ hu huN)
  rcases hM with hP | hP
  · obtain ⟨m₁, m₂, v₀, hv₀, v₁, hv₁, v₂, hv₂, c01, c02, c12, o0, o1, o2, d1, d2, d12⟩ :=
      E4Cover.sp6_three hP hd
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective N m₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk'_surjective N m₂
    rw [conjSub_map] at hv₁ hv₂ d1 d2
    rw [conjSub_map, conjSub_map] at d12
    exact E4Cover.exists_three_of_mk hN2 hK2 hv₀ hv₁ hv₂ c01 c02 c12 o0 o1 o2 d1 d2 d12
  · obtain ⟨-, h3, hcomm⟩ := e4CoverNbrs_proved X N K u hN2 hNc hΩ hq hu huN htw (Or.inr hP)
    obtain ⟨B₁, B₂, B₃, h12, -, -, hB⟩ := Set.ncard_eq_three.mp (h3 hP)
    have hB₁ : B₁ ∈ omegaNbr (CoreAssembly.conjClass K) K := by
      rw [hB]
      exact Set.mem_insert _ _
    have hB₂ : B₂ ∈ omegaNbr (CoreAssembly.conjClass K) K := by
      rw [hB]
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hcm : ∀ B ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K),
        ∀ B' ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K), B ≠ B' →
          ∀ x ∈ B, ∀ y ∈ B', QuotientGroup.mk' N x * QuotientGroup.mk' N y =
            QuotientGroup.mk' N y * QuotientGroup.mk' N x := by
      intro B hB B' hB' hne x hx y hy
      have h1 := hcomm B hB B' hB' hne x hx y hy
      rw [← QuotientGroup.eq_one_iff] at h1
      change QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 at h1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc QuotientGroup.mk' N x * QuotientGroup.mk' N y =
          QuotientGroup.mk' N x * QuotientGroup.mk' N y * (QuotientGroup.mk' N x)⁻¹ *
            (QuotientGroup.mk' N y)⁻¹ * (QuotientGroup.mk' N y * QuotientGroup.mk' N x) := by
            group
        _ = QuotientGroup.mk' N y * QuotientGroup.mk' N x := by rw [h1, one_mul]
    have hK : K ∈ insert K (omegaNbr (CoreAssembly.conjClass K) K) := Set.mem_insert _ _
    have hB₁' := Set.mem_insert_of_mem K hB₁
    have hB₂' := Set.mem_insert_of_mem K hB₂
    obtain ⟨g₁, rfl⟩ := hB₁.1
    obtain ⟨g₂, rfl⟩ := hB₂.1
    obtain ⟨a, ha, b, hb, hab⟩ := PhilipHall.Frame.TwinDisc.ExitE4.exists_noncomm hΩ h2
      (CoreAssembly.mem_conjClass_self K)
    have hKN := E4Cover.inf_eq_bot_of_mem_conjClass hq hΩ hu huN K
      (CoreAssembly.mem_conjClass_self K)
    obtain ⟨k, hk, hk2⟩ : ∃ k ∈ K, k ^ 2 ≠ 1 := by
      by_contra hall
      push Not at hall
      have hau := (hu.unique a ha (by rw [← sq]; exact hall a ha))
      have hbu := (hu.unique b hb (by rw [← sq]; exact hall b hb))
      apply hab
      rcases hau with rfl | rfl <;> rcases hbu with rfl | rfl <;> group
    have hsq : ∀ g : X, (QuotientGroup.mk' N (g * k * g⁻¹)) ^ 2 ≠ 1 := by
      intro g h
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      have hkK : k ^ 2 ∈ K ⊓ N := by
        refine Subgroup.mem_inf.mpr ⟨K.pow_mem hk 2, ?_⟩
        have e1 : (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := conj_pow
        rw [e1] at h
        have h' := (inferInstance : N.Normal).conj_mem _ h g⁻¹
        have e2 : g⁻¹ * (g * k ^ 2 * g⁻¹) * g⁻¹⁻¹ = k ^ 2 := by group
        rwa [e2] at h'
      rw [hKN, Subgroup.mem_bot] at hkK
      exact hk2 hkK
    have hk0 : QuotientGroup.mk' N k ^ 2 ≠ 1 := by simpa using hsq 1
    refine E4Cover.exists_three_of_mk hN2 hK2 (Subgroup.mem_map_of_mem _ hk)
      (Subgroup.mem_map_of_mem _ (conj_mem_conjSub hk g₁))
      (Subgroup.mem_map_of_mem _ (conj_mem_conjSub hk g₂))
      (hcm K hK _ hB₁' hB₁.2.1.symm _ hk _ (conj_mem_conjSub hk g₁))
      (hcm K hK _ hB₂' hB₂.2.1.symm _ hk _ (conj_mem_conjSub hk g₂))
      (hcm _ hB₁' _ hB₂' h12 _ (conj_mem_conjSub hk g₁) _ (conj_mem_conjSub hk g₂))
      hk0 (hsq g₁) (hsq g₂) (c.map_ne_of_ne (CoreAssembly.mem_conjClass_self K) ⟨g₁, rfl⟩ hB₁.2.1)
      (c.map_ne_of_ne (CoreAssembly.mem_conjClass_self K) ⟨g₂, rfl⟩ hB₂.2.1)
      (c.map_ne_of_ne ⟨g₂, rfl⟩ ⟨g₁, rfl⟩ h12)

section Orb

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem conjClass_subgroupOf_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) :
    CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)) =
      restrictFamily Φ (Vtx.orbGrp Φ K) := by
  have hcl := h.hyp.conjInvariant
  ext L
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨conjSub (c : Q) K, hcl _ K hK,
      Vtx.conjSub_le_orbGrp _ ⟨(c : Q), Vtx.orbGrp_le hcl hK c.2⟩, conjSub_subgroupOf _ c K⟩
  · rintro ⟨L, hL, hLX, rfl⟩
    obtain ⟨g, hg, rfl⟩ := exists_orbGrp_conj_of_le h4 h hO hn hK hL hLX
    exact ⟨⟨g, hg⟩, conjSub_subgroupOf _ ⟨g, hg⟩ K⟩

theorem iSup_conjSub_subgroupOf_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) :
    (⨆ c : ↥(Vtx.orbGrp Φ K), conjSub c (K.subgroupOf (Vtx.orbGrp Φ K))) = ⊤ := by
  have hcl := h.hyp.conjInvariant
  have hcomm := Vtx.commute_conj_of_not_conj h4 h hO hn hK
  apply Subgroup.map_injective (Vtx.orbGrp Φ K).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have e2 : ∀ c : ↥(Vtx.orbGrp Φ K), (conjSub c (K.subgroupOf (Vtx.orbGrp Φ K))).map
      (Vtx.orbGrp Φ K).subtype = conjSub (c : Q) K := by
    intro c
    rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
    exact Vtx.conjSub_le_orbGrp _ ⟨(c : Q), Vtx.orbGrp_le hcl hK c.2⟩
  simp_rw [e2]
  exact (Vtx.orbGrp_eq_iSup hcl hK hcomm).symm

theorem exists_three_of_twinE4_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q}
    (hK : K ∈ Φ) {u : Q} (hu : IsUniqueInvolution K u)
    (hu2 : ¬ ∃ P : Subgroup ↥(Vtx.orbGrp Φ K), P.Normal ∧ IsPGroup 2 ↥P ∧
      (⟨u, Vtx.le_orbGrp K hu.mem⟩ : ↥(Vtx.orbGrp Φ K)) ∈ P)
    (hE4 : PhilipHall.Frame.TwinE4 ↥(Vtx.orbGrp Φ K)) :
    ∃ K₁ ∈ Φ, ∃ K₂ ∈ Φ, ∃ P : Subgroup Q, IsPGroup 2 ↥P ∧ K₁ ≠ K ∧ K₂ ≠ K ∧ K₁ ≠ K₂ ∧
      2 < Nat.card ↥(K ⊓ P) ∧ 2 < Nat.card ↥(K₁ ⊓ P) ∧ 2 < Nat.card ↥(K₂ ⊓ P) := by
  have hcl := h.hyp.conjInvariant
  have hKX : K ≤ Vtx.orbGrp Φ K := Vtx.le_orbGrp K
  have hOX : classicalInvolutionOddCore ↥(Vtx.orbGrp Φ K) = ⊥ :=
    CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hK) hO
  have hfam := conjClass_subgroupOf_orbGrp h4 h hO hn hK
  have hX : TypeRFam 3 (CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K))) := by
    rw [hfam]
    exact h.restrict _
  have hu' := isUniqueInvolution_subgroupOf hu hKX
  obtain ⟨hZ2, huZ, hM, hq⟩ := E4Cover.twinE4_center hX
    (iSup_conjSub_subgroupOf_orbGrp h4 h hO hn hK) hOX hu' hu2 hE4
  obtain ⟨K₁, hK₁, K₂, hK₂, P, hP, h1, h2, h12, c0, c1, c2⟩ :=
    e4CoverThree_proved _ (Subgroup.center _) _ _ hZ2 le_rfl hX.hyp hq hu' huZ
      (hX.noTwins _ (CoreAssembly.mem_conjClass_self _)) hM
  have hinj' := (Vtx.orbGrp Φ K).subtype_injective
  have hinj := Subgroup.map_injective hinj'
  have hmapK : (K.subgroupOf (Vtx.orbGrp Φ K)).map (Vtx.orbGrp Φ K).subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKX
  have hmem : ∀ L ∈ CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)),
      L.map (Vtx.orbGrp Φ K).subtype ∈ Φ := by
    intro L hL
    rw [hfam] at hL
    obtain ⟨L', hL', hL'X, rfl⟩ := hL
    rw [Subgroup.map_subgroupOf_eq_of_le hL'X]
    exact hL'
  have hcard : ∀ A : Subgroup ↥(Vtx.orbGrp Φ K), Nat.card ↥(A.map (Vtx.orbGrp Φ K).subtype ⊓
      P.map (Vtx.orbGrp Φ K).subtype) = Nat.card ↥(A ⊓ P) := by
    intro A
    rw [← Subgroup.map_inf_eq _ _ _ hinj']
    exact Subgroup.card_map_of_injective hinj'
  have hc0 := hcard (K.subgroupOf (Vtx.orbGrp Φ K))
  rw [hmapK] at hc0
  refine ⟨K₁.map _, hmem K₁ hK₁, K₂.map _, hmem K₂ hK₂, P.map (Vtx.orbGrp Φ K).subtype,
    hP.map _, fun e => h1 (hinj (e.trans hmapK.symm)), fun e => h2 (hinj (e.trans hmapK.symm)),
    fun e => h12 (hinj e), ?_, ?_, ?_⟩
  · rw [hc0]
    exact c0
  · rw [hcard]
    exact c1
  · rw [hcard]
    exact c2

end Orb

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.not_twinE4_secOrb (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z) :
    ¬ PhilipHall.Frame.TwinE4
      ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) := by
  intro hE4
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have hu2 : ¬ ∃ P : Subgroup
      ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)), P.Normal ∧
      IsPGroup 2 ↥P ∧ (⟨_, Vtx.le_orbGrp _ hzb.mem⟩ :
        ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) ∈ P := by
    rintro ⟨P, hPn, hP2, hzP⟩
    refine hO2 ⟨P, hPn, hP2, fun c hc => ?_⟩
    obtain ⟨⟨y, hyY⟩, hy, hyc⟩ := hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hyz : (⟨z ^ k, hyY⟩ : ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t))) =
        ⟨z, hzY⟩ ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow])
    have hck : c = (⟨_, Vtx.le_orbGrp _ hzb.mem⟩ :
        ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) ^ k := by
      apply Subtype.ext
      rw [SubgroupClass.coe_zpow, ← hyc, hyz, map_zpow]
    rw [hck]
    exact P.zpow_mem hzP k
  obtain ⟨K₁, hK₁, K₂, hK₂, P, hP, h1, h2, h12, c0, c1, c2⟩ :=
    exists_three_of_twinE4_orbGrp h4 h.secFam secQuot_oddCore_eq_bot hs.natCard_secQuot_lt
      (secImg_mem hs.xMem_K) hzb hu2 hE4
  obtain ⟨L₁, hL₁, rfl⟩ := mem_secFam_iff.mp hK₁
  obtain ⟨L₂, hL₂, rfl⟩ := mem_secFam_iff.mp hK₂
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hL₁ hL₂ (Ne.symm h1)
    (Ne.symm h2) h12 hP c0 c1 c2

theorem tightC264NoTwinE4_of (h4 : Thm4RBelow 3 n) : TightC264NoTwinE4 n := by
  intro _ Y _ _ Rd Sd z J S R T W t hs _ hE _ hO2
  exact hs.not_twinE4_secOrb h4 hE hO2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
