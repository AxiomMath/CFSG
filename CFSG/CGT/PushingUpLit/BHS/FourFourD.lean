module

public import CFSG.CGT.PushingUpLit.BHS.FourFourC
public import CFSG.CGT.PushingUpLit.BHS.FourOne
public import CFSG.CGT.PushingUpLit.BHS.FourOneD
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem Hyp41.sylowGood_of_lamSet {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M L : Subgroup (MulAut V)} (h : Hyp41 P D) (hL : L ∈ lamSet P D M) : SylowGood L := by
  intro S hS
  have hSD : S ∈ D := ((hL.2.2.1 S).2 hS).1
  exact ⟨h.quad S hSD, h.card_eq S hSD⟩

theorem IsSLNatSection.exists_sylow_ne {L : Subgroup (MulAut V)} {n : ℕ}
    (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) {S : Subgroup (MulAut V)}
    (_hS : IsSylowOf 2 S L) : ∃ S', IsSylowOf 2 S' L ∧ S' ≠ S := by
  have h1 : 1 < Set.ncard {S : Subgroup (MulAut V) | IsSylowOf 2 S L} := by
    rw [h.ncard_sylows hn]
    have := Nat.one_lt_two_pow (n := n) (by omega)
    omega
  obtain ⟨S', hS', hne⟩ := Set.exists_ne_of_one_lt_ncard h1 S
  exact ⟨S', hS', hne⟩

theorem IsSLNatSection.commV_sup_fixV {L : Subgroup (MulAut V)} {n : ℕ}
    (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) (hG : SylowGood L) :
    commV L ⊔ fixV L = ⊤ := by
  obtain ⟨S, hS, -⟩ := h.exists_sylow_mem_fixV hn hG 1
  obtain ⟨S', hS', hne⟩ := h.exists_sylow_ne hn hS
  have h1 := (h.fixV_inf_sup_sylow hn hG hS hS' hne.symm).2
  rw [h.fixV_sylow_eq hn hG hS, h.fixV_sylow_eq hn hG hS'] at h1
  rw [eq_top_iff, ← h1]
  exact sup_le (sup_le (le_sup_of_le_left (B19.commV_mono hS.1)) le_sup_right)
    (sup_le (le_sup_of_le_left (B19.commV_mono hS'.1)) le_sup_right)

omit [Finite V] in
theorem IsSLNatSection.of_sup_eq_top {L : Subgroup (MulAut V)} {n : ℕ}
    (h : IsSLNatSection L ⊤ (fixV L) n) {W : Subgroup V}
    (hinv : ∀ x ∈ L, ∀ p ∈ W, x p ∈ W) (hsup : W ⊔ fixV L = ⊤) :
    IsSLNatSection L W (W ⊓ fixV L) n := by
  obtain ⟨-, θ, β, hsurj, hker, hact⟩ := h
  have hker' : ∀ f ∈ fixV L, β ⟨f, trivial⟩ = 1 := fun f hf => by
    have : (⟨f, trivial⟩ : ↥(⊤ : Subgroup V)) ∈ β.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hf
    exact this
  refine ⟨hinv, θ, β.comp (Subgroup.inclusion le_top), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hsurj y
    have hv' : (v : V) ∈ W ⊔ fixV L := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, f, hf, hwf⟩ := Subgroup.mem_sup.1 hv'
    refine ⟨⟨w, hw⟩, ?_⟩
    have hvw : v = ⟨w, trivial⟩ * ⟨f, trivial⟩ := Subtype.ext hwf.symm
    show β ⟨w, trivial⟩ = y
    rw [← hv, hvw, map_mul, hker' f hf, mul_one]
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show β ⟨(p : V), trivial⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun hp => ⟨p.2, hp⟩, fun hp => hp.2⟩
  · intro x p hp
    exact hact x ⟨(p : V), trivial⟩ trivial

omit [Finite V] in
theorem map_commV_sup_of_fix {g : MulAut V} {Z : Subgroup V} (hg : ∀ z ∈ Z, g z = z)
    (K : Subgroup (MulAut V)) :
    (commV K ⊔ Z).map g.toMonoidHom = commV (conjSub g K) ⊔ Z := by
  have hZ : Z.map g.toMonoidHom = Z := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g y ∈ Z
      rw [hg y hy]
      exact hy
    · intro hz
      exact ⟨z, hz, hg z hz⟩
  rw [Subgroup.map_sup, hZ]
  exact congrArg (· ⊔ Z) (B19.commV_map_conj g K).symm

omit [Finite V] in
theorem card_commV_sup_conj {g : MulAut V} {Z : Subgroup V} (hg : ∀ z ∈ Z, g z = z)
    (K : Subgroup (MulAut V)) :
    Nat.card ↥(commV (conjSub g K) ⊔ Z) = Nat.card ↥(commV K ⊔ Z) := by
  rw [← map_commV_sup_of_fix hg K]
  exact Subgroup.card_map_of_injective g.injective

theorem card_sup_le_of_card_eq {H₁ H₂ Z : Subgroup V} {c : ℕ} (h₁ : Nat.card H₁ = c * Nat.card Z)
    (h₂ : Nat.card H₂ = c * Nat.card Z) (hZ₁ : Z ≤ H₁) (hZ₂ : Z ≤ H₂) :
    Nat.card ↥(H₁ ⊔ H₂) ≤ c ^ 2 * Nat.card Z := by
  have hinf := card_sup_mul_card_inf' (X := H₁) (Y := H₂) fun a _ b _ => mul_comm a b
  have hle : Nat.card Z ≤ Nat.card ↥(H₁ ⊓ H₂) := Subgroup.card_le_of_le (le_inf hZ₁ hZ₂)
  rw [h₁, h₂] at hinf
  have hpos : 0 < Nat.card Z := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(H₁ ⊔ H₂) * Nat.card Z ≤ Nat.card ↥(H₁ ⊔ H₂) * Nat.card ↥(H₁ ⊓ H₂) :=
        Nat.mul_le_mul_left _ hle
    _ = c * Nat.card Z * (c * Nat.card Z) := hinf
    _ = c ^ 2 * Nat.card Z * Nat.card Z := by ring

structure Hyp413Comm (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (M L A B : Subgroup (MulAut V)) (n : ℕ) : Prop where
  hyp : Hyp41 P D
  lam : L ∈ lamSet P D M
  one_le : 1 ≤ n
  sl : IsSLNatSection L ⊤ (fixV L) n
  memA : A ∈ D
  leA : A ≤ L
  memB : B ∈ D
  not_le : ¬ B ≤ L
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  noncomm : ∃ l ∈ L, ∃ b ∈ B, l * b ≠ b * l

namespace Hyp413Comm

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
  {M L A B : Subgroup (MulAut V)} {n : ℕ}

omit [Finite V] in
theorem ne (d : Hyp413Comm P D M L A B n) : A ≠ B := fun h => d.not_le (h ▸ d.leA)

omit [Finite V] in
theorem sylowGood (d : Hyp413Comm P D M L A B n) : SylowGood L :=
  d.hyp.sylowGood_of_lamSet d.lam

omit [Finite V] in
theorem sylowA (d : Hyp413Comm P D M L A B n) : IsSylowOf 2 A L :=
  (d.lam.2.2.1 A).1 ⟨d.memA, d.leA⟩

theorem card_A (d : Hyp413Comm P D M L A B n) : Nat.card A = 2 ^ n :=
  d.sl.sylow_card d.one_le d.sylowA

omit [Finite V] in
theorem card_V (d : Hyp413Comm P D M L A B n) : Nat.card V = 4 ^ n * Nat.card (fixV L) :=
  d.sl.card_V d.one_le

theorem exists_conj (d : Hyp413Comm P D M L A B n) :
    ∃ A' : Subgroup (MulAut V), ∃ x ∈ L, ∃ g ∈ L ⊔ B, IsSylowOf 2 A' L ∧ A ⊔ A' = L ∧
      A' = conjSub x A ∧ B = conjSub g A' := by
  obtain ⟨A', hA'S, hne⟩ := d.sl.exists_sylow_ne d.one_le d.sylowA
  have hA'D : A' ∈ D := ((d.lam.2.2.1 A').2 hA'S).1
  have hsup : A ⊔ A' = L := d.sl.sylow_sup_eq d.one_le d.sylowA hA'S hne.symm
  obtain ⟨x, hx, hA'x⟩ := IsSLNatSection.sylow_conj d.sylowA hA'S
  have hnc : ¬ ∀ a ∈ A', ∀ b ∈ B, a * b = b * a := by
    intro hc
    obtain ⟨l, hl, b, hb, hlb⟩ := d.noncomm
    have hle : A ⊔ A' ≤ Subgroup.centralizer (B : Set (MulAut V)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (d.comm a ha z hz).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hc a ha z hz).symm
    rw [hsup] at hle
    exact hlb (Subgroup.mem_centralizer_iff.1 (hle hl) b hb).symm
  rcases d.hyp.four_eight_conj hA'D d.memB with hc | ⟨g, hg, hgB⟩
  · exact absurd hc hnc
  · exact ⟨A', x, hx, g, sup_le_sup_right hA'S.1 B hg, hA'S, hsup, hA'x, hgB⟩

theorem card_B (d : Hyp413Comm P D M L A B n) : Nat.card B = 2 ^ n := by
  obtain ⟨A', -, -, g, -, hA'S, -, -, hBg⟩ := d.exists_conj
  rw [hBg, card_conjSub]
  exact d.sl.sylow_card d.one_le hA'S

theorem card_fixV_AB (d : Hyp413Comm P D M L A B n) :
    Nat.card (fixV (A ⊔ B)) = Nat.card (fixV L) := by
  have h1 := d.hyp.card_prod A d.memA B d.memB (Ne.symm d.ne) d.comm
  rw [d.card_A, d.card_B, d.card_V] at h1
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h4] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

omit [Finite V] in
theorem fixV_AB_inf (d : Hyp413Comm P D M L A B n) :
    fixV (A ⊔ B) ⊓ fixV L = fixV (L ⊔ B) := by
  rw [fixV_sup, fixV_sup]
  apply le_antisymm
  · rintro v ⟨⟨_, hvB⟩, hvL⟩
    exact ⟨hvL, hvB⟩
  · rintro v ⟨hvL, hvB⟩
    exact ⟨⟨fixV_anti d.leA hvL, hvB⟩, hvL⟩

theorem commV_A_le (d : Hyp413Comm P D M L A B n) : commV A ≤ fixV (A ⊔ B) :=
  (B19.commV_mono le_sup_left).trans
    (four_six d.hyp d.memA d.memB d.ne d.comm).2

theorem commV_B_le (d : Hyp413Comm P D M L A B n) : commV B ≤ fixV (A ⊔ B) :=
  (B19.commV_mono le_sup_right).trans
    (four_six d.hyp d.memA d.memB d.ne d.comm).2

theorem commV_sup_eq (d : Hyp413Comm P D M L A B n) :
    commV A ⊔ fixV (L ⊔ B) = fixV (A ⊔ B) := by
  have hX : fixV (A ⊔ B) ≤ commV A ⊔ fixV L :=
    calc fixV (A ⊔ B) ≤ fixV A := fixV_anti le_sup_left
      _ = commV A ⊔ fixV L := d.sl.fixV_sylow_eq d.one_le d.sylowGood d.sylowA
  have h1 := sup_inf_assoc_of_le (fixV L) d.commV_A_le
  rw [inf_eq_right.2 hX, inf_comm, d.fixV_AB_inf] at h1
  exact h1.symm

theorem card_fixV (d : Hyp413Comm P D M L A B n) :
    Nat.card (fixV L) = 2 ^ n * Nat.card (fixV (L ⊔ B)) := by
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (d.hyp.ne_bot B d.memB)
  have hbB : (b : MulAut V) ∈ B := b.2
  have hb1' : (b : MulAut V) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hfix : fixV (Subgroup.zpowers (b : MulAut V)) = fixV B :=
    d.hyp.fixV_eq B d.memB b hbB hb1'
  have hker : (NatSL2.commMap (b : MulAut V)).ker = fixV B := by
    rw [NatSL2.ker_commMap, hfix]
  have hrange : Nat.card (NatSL2.commMap (b : MulAut V)).range = 2 ^ n := by
    have h1 := card_commV_zpowers_mul (b : MulAut V)
    rw [NatSL2.commV_zpowers_eq_range, hfix] at h1
    have h2 := d.hyp.card_eq B d.memB
    rw [d.card_B] at h2
    have hpos : 0 < Nat.card (fixV B) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, h2]
  generalize NatSL2.commMap (b : MulAut V) = φ at hker hrange
  have hmap : (fixV L).map φ = φ.range := by
    refine le_antisymm (Subgroup.map_le_range φ _) ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ fixV A ⊔ fixV B := by
      rw [(four_six d.hyp d.memA d.memB d.ne d.comm).1]
      exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [d.sl.fixV_sylow_eq d.one_le d.sylowGood d.sylowA] at hv₁
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hv₁
    refine ⟨f, hf, ?_⟩
    have hu1 : φ u = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact fixV_anti le_sup_right (d.commV_A_le hu)
    have hv2 : φ v₂ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hv₂
    rw [map_mul, map_mul, hu1, hv2, one_mul, mul_one]
  have hcard := B1More.card_map_mul_card_inf_ker (fixV L) φ
  rw [hmap, hrange, hker, ← fixV_sup] at hcard
  exact hcard.symm

theorem card_commV_sup (d : Hyp413Comm P D M L A B n) :
    Nat.card ↥(commV A ⊔ fixV (L ⊔ B)) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) := by
  rw [d.commV_sup_eq, d.card_fixV_AB, d.card_fixV]

theorem card_V_star (d : Hyp413Comm P D M L A B n) :
    Nat.card V = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) := by
  rw [d.card_V, d.card_fixV]
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]
  ring

theorem commV_B_sup_eq (d : Hyp413Comm P D M L A B n) :
    commV B ⊔ fixV (L ⊔ B) = fixV (A ⊔ B) := by
  obtain ⟨A', x, hx, g, hg, hA'S, -, hA'x, hBg⟩ := d.exists_conj
  have hxfix : ∀ z ∈ fixV (L ⊔ B), x z = z := fun z hz => hz x (Subgroup.mem_sup_left hx)
  have hgfix : ∀ z ∈ fixV (L ⊔ B), g z = z := fun z hz => hz g hg
  have hle : commV B ⊔ fixV (L ⊔ B) ≤ fixV (A ⊔ B) :=
    sup_le d.commV_B_le (fixV_anti (sup_le_sup_right d.leA B))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card ↥(commV B ⊔ fixV (L ⊔ B)) = Nat.card ↥(commV A ⊔ fixV (L ⊔ B)) := by
    have e1 : commV B = commV (conjSub g A') := congrArg commV hBg
    rw [e1, card_commV_sup_conj hgfix A', hA'x, card_commV_sup_conj hxfix A]
  rw [h1, d.commV_sup_eq]

theorem commV_sup_LB (d : Hyp413Comm P D M L A B n) :
    commV (L ⊔ B) ⊔ fixV (L ⊔ B) = commV L ⊔ fixV (L ⊔ B) := by
  apply le_antisymm
  · rw [B19.commV_sup]
    refine sup_le (sup_le le_sup_left ?_) le_sup_right
    calc commV B ≤ fixV (A ⊔ B) := d.commV_B_le
      _ = commV A ⊔ fixV (L ⊔ B) := d.commV_sup_eq.symm
      _ ≤ commV L ⊔ fixV (L ⊔ B) := sup_le_sup_right (B19.commV_mono d.leA) _
  · exact sup_le_sup_right (B19.commV_mono le_sup_left) _

theorem invariant (d : Hyp413Comm P D M L A B n) :
    ∀ g ∈ L ⊔ B, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), g w ∈ commV L ⊔ fixV (L ⊔ B) := by
  have hXW : fixV (A ⊔ B) ≤ commV L ⊔ fixV (L ⊔ B) := by
    rw [← d.commV_sup_eq]
    exact sup_le_sup_right (B19.commV_mono d.leA) _
  have hL' : ∀ x ∈ L, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), x w ∈ commV L ⊔ fixV (L ⊔ B) := by
    intro x hx w hw
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul, hf x (Subgroup.mem_sup_left hx)]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hf)
    have h1 : commV (conjSub x L) = (commV L).map x.toMonoidHom := B19.commV_map_conj x L
    rw [conjSub_self_of_mem hx] at h1
    have h2 : x u ∈ (commV L).map x.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [← h1] at h2
  have hB' : ∀ b ∈ B, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), b w ∈ commV L ⊔ fixV (L ⊔ B) := by
    intro b hb w hw
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul, hf b (Subgroup.mem_sup_right hb)]
    have hc : b u * u⁻¹ ∈ commV B := Subgroup.subset_closure ⟨b, hb, u, rfl⟩
    have h1 : b u * u⁻¹ ∈ commV L ⊔ fixV (L ⊔ B) := hXW (d.commV_B_le hc)
    have h2 : u ∈ commV L ⊔ fixV (L ⊔ B) := Subgroup.mem_sup_left hu
    have h3 : b u * f = b u * u⁻¹ * u * f := by rw [inv_mul_cancel_right]
    rw [h3]
    exact mul_mem (mul_mem h1 h2) (Subgroup.mem_sup_right hf)
  have hLst : L ≤ stabSub (commV L ⊔ fixV (L ⊔ B)) := by
    intro x hx
    rw [mem_stabSub]
    intro u
    refine ⟨fun hxu => ?_, hL' x hx u⟩
    have h1 := hL' x⁻¹ (L.inv_mem hx) _ hxu
    rwa [MulAut.inv_apply_self] at h1
  have hBst : B ≤ stabSub (commV L ⊔ fixV (L ⊔ B)) := by
    intro b hb
    rw [mem_stabSub]
    intro u
    refine ⟨fun hbu => ?_, hB' b hb u⟩
    have h1 := hB' b⁻¹ (B.inv_mem hb) _ hbu
    rwa [MulAut.inv_apply_self] at h1
  intro g hg w hw
  exact (mem_stabSub.1 ((sup_le hLst hBst) hg) w).2 hw

theorem card_W_le (d : Hyp413Comm P D M L A B n) :
    Nat.card ↥(commV L ⊔ fixV (L ⊔ B)) ≤ (2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B)) := by
  obtain ⟨A', x, hx, -, -, -, hsup, hA'x, -⟩ := d.exists_conj
  have hxfix : ∀ z ∈ fixV (L ⊔ B), x z = z := fun z hz => hz x (Subgroup.mem_sup_left hx)
  have hcL : commV L = commV A ⊔ commV A' := by rw [← B19.commV_sup, hsup]
  have hW : commV L ⊔ fixV (L ⊔ B) =
      (commV A ⊔ fixV (L ⊔ B)) ⊔ (commV A' ⊔ fixV (L ⊔ B)) := by
    rw [hcL, sup_sup_distrib_right]
  have hH₂ : Nat.card ↥(commV A' ⊔ fixV (L ⊔ B)) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) := by
    rw [hA'x, card_commV_sup_conj hxfix A, d.card_commV_sup]
  rw [hW]
  exact card_sup_le_of_card_eq d.card_commV_sup hH₂ le_sup_right le_sup_right

theorem sup_fixV_eq_top (d : Hyp413Comm P D M L A B n) :
    (commV L ⊔ fixV (L ⊔ B)) ⊔ fixV L = ⊤ := by
  rw [sup_assoc, sup_eq_right.2 (fixV_anti (le_sup_left : L ≤ L ⊔ B))]
  exact d.sl.commV_sup_fixV d.one_le d.sylowGood

theorem inf_fixV_eq (d : Hyp413Comm P D M L A B n) :
    (commV L ⊔ fixV (L ⊔ B)) ⊓ fixV L = fixV (L ⊔ B) := by
  have hFs : fixV (L ⊔ B) ≤ fixV L := fixV_anti le_sup_left
  have hmul := card_sup_mul_card_inf' (X := commV L ⊔ fixV (L ⊔ B)) (Y := fixV L)
    fun a _ b _ => mul_comm a b
  rw [d.sup_fixV_eq_top, Subgroup.card_top, d.card_V] at hmul
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4] at hmul
  refine (Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right hFs) ?_).symm
  have key : (2 ^ n) ^ 2 * Nat.card (fixV L) * Nat.card ↥((commV L ⊔ fixV (L ⊔ B)) ⊓ fixV L) ≤
      (2 ^ n) ^ 2 * Nat.card (fixV L) * Nat.card ↥(fixV (L ⊔ B)) :=
    calc (2 ^ n) ^ 2 * Nat.card (fixV L) * Nat.card ↥((commV L ⊔ fixV (L ⊔ B)) ⊓ fixV L)
        = Nat.card ↥(commV L ⊔ fixV (L ⊔ B)) * Nat.card (fixV L) := hmul
      _ ≤ (2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B)) * Nat.card (fixV L) :=
        Nat.mul_le_mul_right _ d.card_W_le
      _ = (2 ^ n) ^ 2 * Nat.card (fixV L) * Nat.card ↥(fixV (L ⊔ B)) := by ring
  exact Nat.le_of_mul_le_mul_left key (Nat.mul_pos (by positivity) Nat.card_pos)

end Hyp413Comm

theorem four_thirteen_comm {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M L A B : Subgroup (MulAut V)} (h : Hyp41 P D) (hL : L ∈ lamSet P D M) {n : ℕ} (hn : 1 ≤ n)
    (hSL : IsSLNatSection L ⊤ (fixV L) n) (hA : A ∈ D) (hAL : A ≤ L) (hB : B ∈ D)
    (hBL : ¬ B ≤ L) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hLB : ∃ l ∈ L, ∃ b ∈ B, l * b ≠ b * l) :
    Nat.card A = 2 ^ n ∧ Nat.card B = 2 ^ n ∧
    (commV A ⊔ fixV (L ⊔ B) = fixV (A ⊔ B) ∧ commV B ⊔ fixV (L ⊔ B) = fixV (A ⊔ B)) ∧
    Nat.card ↥(commV A ⊔ fixV (L ⊔ B)) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) ∧
    Nat.card V = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) ∧
    Nat.card ↥(fixV L) = 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) ∧
    commV (L ⊔ B) ⊔ fixV (L ⊔ B) = commV L ⊔ fixV (L ⊔ B) ∧
    (∀ g ∈ L ⊔ B, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), g w ∈ commV L ⊔ fixV (L ⊔ B)) ∧
    IsSLNatSection L (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B)) n := by
  have d : Hyp413Comm P D M L A B n := ⟨h, hL, hn, hSL, hA, hAL, hB, hBL, hcomm, hLB⟩
  refine ⟨d.card_A, d.card_B, ⟨d.commV_sup_eq, d.commV_B_sup_eq⟩, d.card_commV_sup,
    d.card_V_star, d.card_fixV, d.commV_sup_LB, d.invariant, ?_⟩
  have hsec := hSL.of_sup_eq_top (fun x hx p hp => d.invariant x (Subgroup.mem_sup_left hx) p hp)
    d.sup_fixV_eq_top
  rwa [d.inf_fixV_eq] at hsec

end CFSG.CGT.PushingUpLit.BHS
