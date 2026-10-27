module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Planes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

variable {G : Type} [Group G] [Finite G]

section Closure

omit [Finite G] in
theorem map_conj_rightConjugate (X : Subgroup G) (p y : G) :
    (rightConjugate X p).map (MulAut.conj y).toMonoidHom = rightConjugate X (p * y⁻¹) := by
  ext x
  rw [mem_rightConjugate_iff, mem_map_equiv, mem_rightConjugate_iff]
  simp only [MulAut.conj_symm_apply, mul_inv_rev, inv_inv]
  group

omit [Finite G] in
theorem rightConjugate_le_conjClosure (X : Subgroup G) {P : Subgroup G} {p : G} (hp : p ∈ P) :
    rightConjugate X p ≤ conjClosure X P :=
  le_iSup (fun q : P => rightConjugate X q) ⟨p, hp⟩

omit [Finite G] in
theorem le_conjClosure_self (X P : Subgroup G) : X ≤ conjClosure X P := by
  have h := rightConjugate_le_conjClosure X P.one_mem
  rwa [rightConjugate_one] at h

theorem le_normalizer_conjClosure (X P : Subgroup G) :
    P ≤ normalizer (conjClosure X P : Set G) := fun q hq =>
  AS76b.mem_normalizer_of_map_conj_le (by
    rw [conjClosure, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [map_conj_rightConjugate]
    exact rightConjugate_le_conjClosure X (P.mul_mem p.2 (P.inv_mem hq)))

theorem mem_normalizer_conjClosure {X P : Subgroup G} {y : G}
    (hyX : y ∈ normalizer (X : Set G)) (hyP : y ∈ normalizer (P : Set G)) :
    y ∈ normalizer (conjClosure X P : Set G) :=
  AS76b.mem_normalizer_of_map_conj_le (by
    rw [conjClosure, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    rw [map_conj_rightConjugate, show (p : G) * y⁻¹ = y⁻¹ * (y * p * y⁻¹) by group,
      ← rightConjugate_mul, (rightConjugate_eq_self_iff X y⁻¹).mpr (inv_mem hyX)]
    exact rightConjugate_le_conjClosure X ((mem_normalizer_iff.mp hyP p).mp p.2))

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer_left {X N : Subgroup G}
    (hX : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  set M := normalizer (N : Set G)
  have hNM : N ≤ M := le_normalizer
  have : (N.subgroupOf M).Normal := normal_in_normalizer
  have hc : ∀ Y : Subgroup G, Y ≤ M → Nat.card (Y.subgroupOf M) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have h1 := relIndex_mul_card (H := N.subgroupOf M) (K := X.subgroupOf M ⊔ N.subgroupOf M)
  have h2 := relIndex_mul_card (H := N.subgroupOf M) (K := X.subgroupOf M)
  rw [relIndex_sup_right, inf_of_le_left (le_sup_right : N.subgroupOf M ≤ _)] at h1
  rw [← subgroupOf_sup hX hNM, hc _ (sup_le hX hNM), hc N hNM] at h1
  have hinf : X.subgroupOf M ⊓ N.subgroupOf M = (X ⊓ N).subgroupOf M :=
    Subgroup.ext fun _ => Iff.rfl
  rw [inf_comm, hinf, hc _ (inf_le_left.trans hX), hc X hX] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem eq_or_eq_of_index_four {K H X : Subgroup G} {y : G}
    (hidx : K.relIndex H = 4) (hKX : K ≤ X) (hXH : X ≤ H) (hyK : y ∈ normalizer (K : Set G))
    (hyX : y ∈ normalizer (X : Set G)) (hfix : ∀ h ∈ H, y * h * y⁻¹ * h⁻¹ ∈ K → h ∈ K) :
    X = K ∨ X = H := by
  by_contra hne
  push Not at hne
  obtain ⟨hXK, hXH'⟩ := hne
  have hm := relIndex_mul_relIndex K X H hKX hXH
  rw [hidx] at hm
  have h1 : K.relIndex X ≠ 1 := fun h => hXK (le_antisymm (relIndex_eq_one.mp h) hKX)
  have h2 : X.relIndex H ≠ 1 := fun h => hXH' (le_antisymm hXH (relIndex_eq_one.mp h))
  have hidx2 : K.relIndex X = 2 := by
    have hdvd : K.relIndex X ∣ 4 := ⟨_, hm.symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : K.relIndex X <;> first | rfl | omega
  obtain ⟨x, hxX, hxK⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hKX (Ne.symm hXK))
  have hyx : y * x * y⁻¹ ∈ X := (mem_normalizer_iff.mp hyX x).mp hxX
  have hyxK : y * x * y⁻¹ ∉ K := fun h => hxK (by
    have := (mem_normalizer_iff.mp (inv_mem hyK) _).mp h
    simpa [mul_assoc] using this)
  have hidx' : (K.subgroupOf X).index = 2 := hidx2
  have hmem := (mul_mem_iff_of_index_two hidx' (a := ⟨y * x * y⁻¹, hyx⟩)
    (b := ⟨x⁻¹, X.inv_mem hxX⟩)).mpr (by
      rw [mem_subgroupOf, mem_subgroupOf]
      exact iff_of_false hyxK (fun h => hxK (by simpa using K.inv_mem h)))
  rw [mem_subgroupOf] at hmem
  exact hxK (hfix x (hXH hxX) hmem)

end Closure

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem conjClosure_le_sec2S : conjClosure (F ⊓ A) (sec2P E) ≤ sec2S A R E F := by
  refine iSup_le fun ⟨p, hp⟩ x hx => ?_
  rw [mem_rightConjugate_iff] at hx
  have hc := mem_centralizerMod_of_mem_sec2P h11 hE16 hF hL hodd ((sec2P E).inv_mem hp) hx.1
  rw [inv_inv] at hc
  have hx' : x = (p * x * p⁻¹) * ((p * x * p⁻¹)⁻¹ * p⁻¹ * (p * x * p⁻¹) * p) := by group
  rw [hx']
  exact mul_mem (mem_sup_left hx.1) (mem_sup_right hc)

theorem mem_of_conj_mul_inv_mem {y : G} (hyA : y ∈ A)
    (hyfix : ∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1) {c : G}
    (hc : c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
    (hcy : c⁻¹ * (y * c * y⁻¹) ∈ E) : c ∈ E := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  rw [← hPR]
  refine ⟨(mem_centralizerMod.mp hc).1, centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => ?_)⟩
  set e := c⁻¹ * (y * c * y⁻¹) with he
  have hk : r⁻¹ * c⁻¹ * r * c ∈ sec2Z A E F := (mem_centralizerMod.mp hc).2.2 r (mem_sup_left hr)
  have hrE : r ∈ E := hF.R_le_E hr
  have hyr : y * r * y⁻¹ = r := by
    rw [mem_centralizer_iff.mp (hF.sylowR.le hr) y hyA, mul_inv_cancel_right]
  have hd : y * c * y⁻¹ = c * e := by rw [he]; group
  have hre : r * e = e * r := hD.comm r hrE e hcy
  have hke : (r⁻¹ * c⁻¹ * r * c) * e = e * (r⁻¹ * c⁻¹ * r * c) := hD.comm _ (hZE hk) e hcy
  have hre' : r⁻¹ * e⁻¹ = e⁻¹ * r⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hre]
  have hfix : y * (r⁻¹ * c⁻¹ * r * c) * y⁻¹ = r⁻¹ * c⁻¹ * r * c := by
    calc y * (r⁻¹ * c⁻¹ * r * c) * y⁻¹
        = (y * r * y⁻¹)⁻¹ * (y * c * y⁻¹)⁻¹ * (y * r * y⁻¹) * (y * c * y⁻¹) := by group
      _ = r⁻¹ * (c * e)⁻¹ * r * (c * e) := by rw [hyr, hd]
      _ = (r⁻¹ * e⁻¹) * c⁻¹ * r * c * e := by group
      _ = e⁻¹ * ((r⁻¹ * c⁻¹ * r * c) * e) := by rw [hre']; group
      _ = r⁻¹ * c⁻¹ * r * c := by rw [hke]; group
  have h1 := hyfix _ (hF.sec2Z_eq ▸ hk) hfix
  calc r * c = r * c * (r⁻¹ * c⁻¹ * r * c)⁻¹ := by rw [h1, inv_one, mul_one]
    _ = c * r := by group

theorem eq_or_eq_of_le_centralizerMod {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyfix : ∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1) {X : Subgroup G} (hEX : E ≤ X)
    (hXC : X ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
    (hyX : y ∈ normalizer (X : Set G)) :
    X = E ∨ X = centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  refine eq_or_eq_of_index_four hCidx hEX hXC hyE hyX fun c hc h => ?_
  refine mem_of_conj_mul_inv_mem h11 hE16 hF hL hodd hyA hyfix hc ?_
  have hcN : c ∈ normalizer (E : Set G) := Sec2.sec2P_le E (mem_centralizerMod.mp hc).1
  have := (mem_normalizer_iff.mp (inv_mem hcN) _).mp h
  rw [show c⁻¹ * (y * c * y⁻¹) = c⁻¹ * (y * c * y⁻¹ * c⁻¹) * c⁻¹⁻¹ by group]
  exact this

theorem mem_centralizerMod_of_commutator_mem {f p : G} (hf : f ∈ F) (hfE : f ∉ E)
    (hp : p ∈ sec2P E) (h : f⁻¹ * p⁻¹ * f * p ∈ E) :
    p ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hpN := Sec2.sec2P_le E hp
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQ : rightConjugate R p ∈ pointsIn R E := rightConjugate_mem_pointsIn hD.self_mem hpN
  have hfQ : f ∈ normalizer (rightConjugate R p : Set G) := by
    refine Sec2.mem_normalizer_of_forall_conj_mem fun q hq => ?_
    rw [mem_rightConjugate_iff] at hq ⊢
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, p⁻¹ * r * p = q := ⟨p * q * p⁻¹, hq, by group⟩
    have hfr : f * r * f⁻¹ = r := by rw [hFcomm f hf r (hF.R_le_F hr), mul_inv_cancel_right]
    have he : p * (f⁻¹ * p⁻¹ * f * p)⁻¹ * p⁻¹ ∈ E :=
      (mem_normalizer_iff.mp hpN _).mp (E.inv_mem h)
    have hcomm := hD.comm _ he _ (hF.R_le_E hr)
    rw [show p * (f * (p⁻¹ * r * p) * f⁻¹) * p⁻¹ = r from ?_]
    · exact hr
    calc p * (f * (p⁻¹ * r * p) * f⁻¹) * p⁻¹
        = f * ((p * (f⁻¹ * p⁻¹ * f * p)⁻¹ * p⁻¹) * r) *
            (p * (f⁻¹ * p⁻¹ * f * p)⁻¹ * p⁻¹)⁻¹ * f⁻¹ := by group
      _ = f * r * f⁻¹ := by rw [hcomm]; group
      _ = r := hfr
  have hle : rightConjugate R p ≤ E ⊓ F := by
    by_contra hnot
    exact hfE (mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd hf hQ hnot hfQ)
  exact mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hp hle

theorem exists_commutator_not_mem :
    ∃ f ∈ F ⊓ A, ∃ p ∈ sec2P E, f⁻¹ * p⁻¹ * f * p ∉ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRc : R ≤ centralizer ((E ⊔ F : Subgroup G) : Set G) := fun r hr => by
    have h := hF.inf_eq_center ▸ hREF hr
    exact h.2
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) (g := g) hF
  have hEFS : E ⊔ F ≤ sec2S A R E F := sup_le hES hFS
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
    have hne : R ≠ ⊥ := fun h => by
      have := hF.cardR
      rw [h, card_bot] at this
      omega
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩
  have hfix : ∀ p ∈ sec2P E, p ∈ normalizer (F : Set G) := fun p hp => by
    have hpN := Sec2.sec2P_le E hp
    have hle : rightConjugate F p ≤ E ⊔ F := fun x hx => by
      rw [mem_rightConjugate_iff] at hx
      obtain ⟨a, ha, s, hs, hx'⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_F hF.F_le hx
      have hxe : x = (a * (a⁻¹ * p⁻¹ * a * p)) * (p⁻¹ * s * p) := by
        rw [show a = p * x * p⁻¹ * s⁻¹ by rw [hx']; group]
        group
      rw [hxe]
      refine mul_mem (mul_mem (mem_sup_right ha.1) (mem_sup_left (hno a ha p hp))) ?_
      exact mem_sup_left ((mem_normalizer_iff.mp (inv_mem hpN) s).mp (hF.R_le_E hs) |>
        fun h => by simpa using h)
    have hFp := AS76b.isElemAbelian_rightConjugate hF.elemF p
    have hD := isElemAbelian_sup_of_le_centralizer hFp hF.elemR
      (fun x hx => mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRc hr) x
        (hle hx)).symm)
    have hcard : Nat.card (rightConjugate F p ⊔ R : Subgroup G) ≤ 64 :=
      card_le_of_isElemAbelian_le_sup_sylow_frame h11 hF hL hodd hR hF.cardR hD
        (sup_le (hle.trans (sup_le hF.E_le hF.F_le)) le_sup_right)
    have hRle : R ≤ rightConjugate F p := by
      have h64 : Nat.card (rightConjugate F p) = 64 := by rw [rightConjugate_card, hF.cardF]
      have heq := eq_of_le_of_card_ge (le_sup_left : rightConjugate F p ≤ rightConjugate F p ⊔ R)
        (by omega)
      rw [heq]
      exact le_sup_right
    rcases eq_or_eq_of_le_sec2S_of_mem_inf h11 hE16 hF hL hodd hFp
        (by rw [rightConjugate_card, hF.cardF]) (hle.trans hEFS) hr (hRle hr) hr1 with h | h
    · exfalso
      apply hF.ne
      have := congrArg (fun X => rightConjugate X p⁻¹) h
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
        (rightConjugate_eq_self_iff E p⁻¹).mpr (inv_mem hpN), eq_comm] at this
    · exact (rightConjugate_eq_self_iff F p).mp h
  have h4 := card_conjSet_sec2P h11 hE16 hF hL hodd
  have hsub : conjSet F (sec2P E) ⊆ {F} := by
    rintro V ⟨p, hp, rfl⟩
    exact (rightConjugate_eq_self_iff F p).mpr (hfix p hp)
  have h1 := Nat.card_mono (Set.finite_singleton F) hsub
  have h2 : Nat.card ({F} : Set (Subgroup G)) = 1 := Nat.card_unique
  omega

theorem sup_inf_sec2P_eq :
    (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) ⊔ E =
      centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hEC, -, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hSP := sec2S_inf_sec2P h11 hE16 hF hL hodd
  have hTS := conjClosure_le_sec2S h11 hE16 hF hL hodd
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  set T := conjClosure (F ⊓ A) (sec2P E)
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hXC : (T ⊓ sec2P E) ⊔ E ≤ C := sup_le (fun x hx => hSP ▸ ⟨hTS hx.1, hx.2⟩) hEC
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyT : y ∈ normalizer (T : Set G) :=
    mem_normalizer_conjClosure (inf_normalizer_le_normalizer_inf ⟨hyF, le_normalizer hyA⟩) hyP
  have hyX : y ∈ normalizer (((T ⊓ sec2P E) ⊔ E : Subgroup G) : Set G) :=
    mem_normalizer_sup (inf_normalizer_le_normalizer_inf ⟨hyT, hyP⟩) hyE
  rcases eq_or_eq_of_le_centralizerMod h11 hE16 hF hL hodd hyA hyE hyfix le_sup_right hXC hyX
    with h | h
  · exfalso
    obtain ⟨f, hf, p, hp, hfp⟩ := exists_commutator_not_mem h11 hE16 hF hL hodd
    apply hfp
    rw [← h]
    refine mem_sup_left ⟨?_, ?_⟩
    · have h1 : f⁻¹ ∈ T := le_conjClosure_self _ _ ((F ⊓ A).inv_mem hf)
      have h2 : p⁻¹ * f * p ∈ T := rightConjugate_le_conjClosure _ hp (by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hf)
      simpa [mul_assoc] using T.mul_mem h1 h2
    · have hfN := Sec2.normalizer_le_normalizer_sec2P E (hF.F_le_normalizer hL hodd hf.1)
      have := (sec2P E).mul_mem ((mem_normalizer_iff.mp (inv_mem hfN) _).mp
        ((sec2P E).inv_mem hp)) hp
      simpa [mul_assoc] using this
  · exact h

theorem conjClosure_sup_eq_sec2S : conjClosure (F ⊓ A) (sec2P E) ⊔ E = sec2S A R E F := by
  have hTS := conjClosure_le_sec2S h11 hE16 hF hL hodd
  obtain ⟨hES, -⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) (g := g) hF
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  refine le_antisymm (sup_le hTS hES) (sup_le (fun f hf => ?_) ?_)
  · obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_F hF.F_le hf
    exact mul_mem (mem_sup_left (le_conjClosure_self _ _ ⟨ha.1, ha.2⟩))
      (mem_sup_right (hF.R_le_E hr))
  · rw [← sup_inf_sec2P_eq h11 hE16 hF hL hodd]
    exact sup_le_sup_right inf_le_left E

theorem four_pow_four_le_card_conjClosure_of_le (h : E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := by
  have hTS := conjClosure_le_sec2S h11 hE16 hF hL hodd
  have hSE := sec2S_le_normalizer_left hF hL hodd
  have hprod := card_sup_mul_card_inf_of_le_normalizer_left (hTS.trans hSE)
  rw [conjClosure_sup_eq_sec2S h11 hE16 hF hL hodd, card_sec2S h11 hE16 hF hL hodd,
    hF.cardE] at hprod
  have hEA : Nat.card (E ⊓ A : Subgroup G) = 16 := card_inf_left hF hodd
  have hle : Nat.card (E ⊓ A : Subgroup G) ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E) ⊓ E :
      Subgroup G) := card_le_of_le (le_inf h inf_le_left)
  rw [hEA] at hle
  nlinarith

theorem exists_commutator_mul_mem {f : G} (hf : f ∈ F) (hfE : f ∉ E) {c : G}
    (hc : c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) :
    ∃ p ∈ sec2P E, (f⁻¹ * p⁻¹ * f * p)⁻¹ * c ∈ E := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨hEC, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  obtain ⟨hEP, hPidx, -⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCN : C ≤ normalizer (E : Set G) := hCP.trans (Sec2.sec2P_le E)
  have hfN : f ∈ normalizer (sec2P E : Set G) :=
    Sec2.normalizer_le_normalizer_sec2P E (hF.F_le_normalizer hL hodd hf)
  have hconj : ∀ p ∈ sec2P E, f⁻¹ * p⁻¹ * f ∈ sec2P E := fun p hp => by
    have := (mem_normalizer_iff.mp (inv_mem hfN) _).mp ((sec2P E).inv_mem hp)
    simpa [mul_assoc] using this
  have hδC : ∀ p ∈ sec2P E, f⁻¹ * p⁻¹ * f * p ∈ C := fun p hp => by
    have := mem_centralizerMod_of_mem_sec2P h11 hE16 hF hL hodd ((sec2P E).inv_mem hp) hf
    simpa using this
  have hEn : (E.subgroupOf C).Normal := ⟨fun x hx c => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hCN c.2) _).mp hx⟩
  have hq : ∀ x y : ↥C, (QuotientGroup.mk x : ↥C ⧸ E.subgroupOf C) = QuotientGroup.mk y ↔
      ((x : G)⁻¹ * y) ∈ E := fun x y => by
    rw [QuotientGroup.eq, mem_subgroupOf, coe_mul, coe_inv]
  let δ : ↥(sec2P E) →* ↥C ⧸ E.subgroupOf C := MonoidHom.mk'
    (fun p => QuotientGroup.mk (⟨f⁻¹ * (p : G)⁻¹ * f * p, hδC p p.2⟩ : ↥C)) (fun p₁ p₂ => by
      rw [← QuotientGroup.mk_mul, hq]
      show (f⁻¹ * ((p₁ : G) * p₂)⁻¹ * f * ((p₁ : G) * p₂))⁻¹ *
        ((f⁻¹ * (p₁ : G)⁻¹ * f * p₁) * (f⁻¹ * (p₂ : G)⁻¹ * f * p₂)) ∈ E
      have hx : (p₁ : G)⁻¹ * (f⁻¹ * (p₁ : G)⁻¹ * f)⁻¹ ∈ sec2P E :=
        (sec2P E).mul_mem ((sec2P E).inv_mem p₁.2) ((sec2P E).inv_mem (hconj p₁ p₁.2))
      have hy : (f⁻¹ * (p₂ : G)⁻¹ * f)⁻¹ ∈ sec2P E := (sec2P E).inv_mem (hconj p₂ p₂.2)
      have hk := (hD.sq_mem_and_commutator_mem hT hCE hx hy).2
      have hk' := (mem_normalizer_iff.mp (inv_mem (Sec2.sec2P_le E p₂.2)) _).mp hk
      have heq : (f⁻¹ * ((p₁ : G) * p₂)⁻¹ * f * ((p₁ : G) * p₂))⁻¹ *
          ((f⁻¹ * (p₁ : G)⁻¹ * f * p₁) * (f⁻¹ * (p₂ : G)⁻¹ * f * p₂)) =
          (p₂ : G)⁻¹ * (((p₁ : G)⁻¹ * (f⁻¹ * (p₁ : G)⁻¹ * f)⁻¹) * (f⁻¹ * (p₂ : G)⁻¹ * f)⁻¹ *
            ((p₁ : G)⁻¹ * (f⁻¹ * (p₁ : G)⁻¹ * f)⁻¹)⁻¹ * (f⁻¹ * (p₂ : G)⁻¹ * f)⁻¹⁻¹) *
            (p₂ : G)⁻¹⁻¹ := by group
      rw [heq]
      exact hk')
  have hker : δ.ker ≤ C.subgroupOf (sec2P E) := fun p hp => by
    rw [MonoidHom.mem_ker] at hp
    have h1 : f⁻¹ * (p : G)⁻¹ * f * p ∈ E := by
      have h0 := (hq ⟨_, hδC p p.2⟩ 1).mp hp
      simp only [OneMemClass.coe_one, mul_one] at h0
      exact inv_mem_iff.mp h0
    exact mem_subgroupOf.mpr (mem_centralizerMod_of_commutator_mem h11 hE16 hF hL hodd hf hfE
      p.2 h1)
  have hCidx' : C.relIndex (sec2P E) = 4 := by
    have := relIndex_mul_relIndex E C (sec2P E) hEC hCP
    rw [hCidx, hPidx] at this
    omega
  have hrange : δ.range = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [← Subgroup.index_ker]
    have h1 : (C.subgroupOf (sec2P E)).index ∣ δ.ker.index := Subgroup.index_dvd_of_le hker
    have h2 : δ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : Nat.card (↥C ⧸ E.subgroupOf C) = 4 := hCidx
    rw [h3]
    have h4 : (C.subgroupOf (sec2P E)).index = 4 := hCidx'
    rw [h4] at h1
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
  obtain ⟨p, hp⟩ := hrange ▸ (mem_top (QuotientGroup.mk (⟨c, hc⟩ : ↥C)) :
    (QuotientGroup.mk (⟨c, hc⟩ : ↥C) : ↥C ⧸ E.subgroupOf C) ∈ (⊤ : Subgroup _))
  exact ⟨p, p.2, (hq _ _).mp hp⟩

end Frame

end CFSG.ComponentClassification.AS81
