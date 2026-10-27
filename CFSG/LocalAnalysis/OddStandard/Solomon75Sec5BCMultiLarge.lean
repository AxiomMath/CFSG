module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiBase
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiQ8
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracFive

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS Equiv.Perm.OnCycleFactors
open scoped commutatorElement

section Fixed

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem bcdLarge_isSec5Inv (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {w : X} (hwZ : w ∈ Z) (hw1 : w ≠ 1) (hws : w * s = s * w) {g : X} {Zs : Subgroup X}
    (hZsg : Zs = Z.map (MulAut.conj g).toMonoidHom)
    (hZs : IsSylowTwoIn (zStar (K0 X n (centralizer ({s} : Set X)))) Zs)
    (hwN : w ∈ normalizer (Zs : Set X)) : IsSec5Inv X Zs w := by
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  have hwC : w ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hws
  have hnot : w ∉ Zs := by
    intro hwZs
    have hzs : w ∈ zStar (K0 X n (centralizer ({s} : Set X))) := hZs.1 hwZs
    obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
    have hBK : B ≤ K0 X n (centralizer ({s} : Set X)) := le_sSup hB
    have hBK' : IsPCompIn 2 (K0 X n (centralizer ({s} : Set X))) B :=
      ⟨hBK, isPComponent_subgroupOf_mono hBK (K0_le n _) hB.isPCompIn.2⟩
    have hwK : w ∈ normalizer ((K0 X n (centralizer ({s} : Set X)) : Subgroup X) : Set X) :=
      mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hwC))
    have hsc : w ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
      normalizes_isPCompIn_of_comm_mem (D := K0 X n (centralizer ({s} : Set X))) hBK' hwK
        (fun b hb => hzs.2.2.2 b (hBK hb))
    exact K0_ne_bot_of_centralizerSection (by rw [sq]; exact hw2) hB hsc
      (sec5_K0_inf_eq_bot h hs hwZ hw1 hws)
  refine ⟨hwN, hnot, hw2, g⁻¹, ?_, ?_⟩
  · rw [hZsg]
    exact ⟨w, hwZ, by simp [MulAut.conj_apply]⟩
  · intro h1
    apply hw1
    have h2 : g * w * g⁻¹ = 1 := by simpa using h1
    have h3 : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [h3, h2]
    group

private theorem bcdLarge_normalizes_E {Zs B : Subgroup X} {w : X}
    (hwN : w ∈ normalizer (Zs : Set X)) (hwB : w ∈ normalizer (B : Set X)) :
    w ∈ normalizer (oTwoPrimeOf (B ⊓ centralizer (Zs : Set X)) : Set X) := by
  have hCZ : w ∈ normalizer ((centralizer (Zs : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ y : X, y ∈ normalizer (Zs : Set X) → ∀ x : X, x ∈ centralizer (Zs : Set X) →
        y * x * y⁻¹ ∈ centralizer (Zs : Set X) := by
      intro y hy x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : y⁻¹ * t * y ∈ Zs := by
        have := (Subgroup.mem_normalizer_iff.1 ((normalizer (Zs : Set X)).inv_mem hy) t).1 ht
        simpa using this
      have hxc := Subgroup.mem_centralizer_iff.1 hx (y⁻¹ * t * y) ht'
      calc t * (y * x * y⁻¹) = y * ((y⁻¹ * t * y) * x) * y⁻¹ := by group
        _ = y * (x * (y⁻¹ * t * y)) * y⁻¹ := by rw [hxc]
        _ = y * x * y⁻¹ * t := by group
    refine ⟨fun hx => key w hwN x hx, fun hx => ?_⟩
    have := key w⁻¹ ((normalizer (Zs : Set X)).inv_mem hwN) _ hx
    simpa [mul_assoc] using this
  exact oTwoPrimeOf_normalizes (A := Subgroup.zpowers w) (H := B ⊓ centralizer (Zs : Set X))
    ((Subgroup.zpowers_le).2 (mem_normalizer_inf hwB hCZ)) (Subgroup.mem_zpowers w)

theorem fixCount_perm_le_four_of_mem_Z (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {w : X} (hwZ : w ∈ Z) (hw1 : w ≠ 1) (hws : w * s = s * w) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (hwB : w ∈ normalizer (B : Set X))
    (MB : AhatModel X n B) : fixCount (MB.perm w hwB) ≤ 4 := by
  have hn : 8 ≤ n := h.maxdeg.1
  have hw2 : w * w = 1 := h.Z_sq_eq_one hwZ
  obtain ⟨g, Zs, S₁, hZsg, hZs, hwQ, hS₁⟩ := exists_mirror_of_Q h hs
    (Q := Subgroup.zpowers w) (isPGroup_zpowers_of_mul_self hw2)
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hws))
  have hwN : w ∈ normalizer (Zs : Set X) := hwQ (Subgroup.mem_zpowers w)
  have hinv : IsSec5Inv X Zs w := bcdLarge_isSec5Inv h hs hwZ hw1 hws hZsg hZs hwN
  obtain ⟨hEc, hEB, hcov⟩ := exists_mirror_comp hS₁ hB
  have hwE := bcdLarge_normalizes_E hwN hwB
  by_contra hcon
  refine false_of_fixCount_ge_five hS₁ hinv hEc hwE (MB.transport hEB hcov) ?_
  rw [MB.perm_transport hn hEB hcov hwE hwB]
  omega

end Fixed

section PermData

variable {X : Type} [Group X] [Finite X] {n : ℕ}

private noncomputable def bcdLargeImg (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B)
    (K : Subgroup X) : Subgroup (Perm (Fin n)) :=
  (K.subgroupOf (normalizer (B : Set X))).map (MB.permHom hn)

private theorem mem_bcdLargeImg (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B)
    {K : Subgroup X} {x : Perm (Fin n)} :
    x ∈ bcdLargeImg hn MB K ↔
      ∃ c : X, ∃ _ : c ∈ normalizer (B : Set X), c ∈ K ∧ MB.permX c = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, c.2, hc, MB.permX_of_mem c.2⟩
  · rintro ⟨c, hcN, hcK, rfl⟩
    exact ⟨⟨c, hcN⟩, hcK, (MB.permX_of_mem hcN).symm⟩

private theorem card_bcdLargeImg_dvd (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B)
    (K : Subgroup X) : Nat.card (bcdLargeImg hn MB K) ∣ Nat.card K := by
  refine (Subgroup.card_map_dvd _ (MB.permHom hn)).trans ?_
  have h1 : Nat.card (K.subgroupOf (normalizer (B : Set X))) =
      Nat.card ↥(K ⊓ normalizer (B : Set X)) := by
    rw [← Subgroup.card_map_of_injective (normalizer (B : Set X)).subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  rw [h1]
  exact Subgroup.card_dvd_of_le inf_le_left

private theorem bcdLarge_oddCoreOf_le_oddTwoCoreOf (H : Subgroup X) :
    oddCoreOf H ≤ oddTwoCoreOf H := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  show QuotientGroup.mk' (pPrimeCore 2 ↥H) y ∈ pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact one_mem _

private theorem bcdLarge_permX_pow (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B) {c : X}
    (hc : c ∈ normalizer (B : Set X)) (m : ℕ) : MB.permX (c ^ m) = MB.permX c ^ m := by
  have h := map_pow (MB.permHom hn) (⟨c, hc⟩ : ↥(normalizer (B : Set X))) m
  rw [MB.permX_of_mem (pow_mem hc m), MB.permX_of_mem hc]
  exact h

private theorem bcdLarge_permData (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B) {u : X}
    (huN : u ∈ normalizer (B : Set X)) (hu2 : u * u = 1) (hτ : MB.perm u huN ≠ 1)
    (hfix : fixCount (MB.perm u huN) ≤ 4) {D : Subgroup X} (hDu : D ≤ centralizer ({u} : Set X))
    (hBD : B ⊓ centralizer ({u} : Set X) ≤ D) {Q : Subgroup X} (hQ8 : Nat.card ↥Q = 8)
    (huQ : u ∈ Q) (hQpow : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) (hyQ : ∃ y ∈ Q, y * y = u)
    (hQo : Q ≤ oddTwoCoreOf D) (hQB : Q ≤ normalizer (B : Set X)) :
    Nonempty (QuatPermDataM n) := by
  classical
  obtain ⟨W, hW8, -, hWτ, hWc, -, hWrange⟩ := q8_perm_data_range hn MB hQB hQ8 huQ hQpow hu2 hτ
  obtain ⟨y, hyQ', hyy⟩ := hyQ
  have hyN : y ∈ normalizer (B : Set X) := hQB hyQ'
  have hτx : MB.permX u = MB.perm u huN := MB.permX_of_mem huN
  have hcomm : ∀ c ∈ oddTwoCoreOf D, c ∈ normalizer (B : Set X) →
      MB.permX c * MB.perm u huN = MB.perm u huN * MB.permX c := by
    intro c hc hcN
    have hcu : c * u = u * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (hDu (oddTwoCoreOf_le D hc))
    rw [← hτx, ← MB.permX_mul hn hcN huN, ← MB.permX_mul hn huN hcN, hcu]
  refine ⟨{
    τ := MB.perm u huN
    W := W
    R := bcdLargeImg hn MB (oddTwoCoreOf D)
    O := bcdLargeImg hn MB (oddCoreOf D)
    y := MB.permX y
    τ_sq := perm_sq_eq_one hn MB huN hu2
    τ_ne := hτ
    fix_le := hfix
    card_W := hW8
    W_zpowers := hWτ
    W_comm := hWc
    W_le_R := ?_
    O_le := ?_
    O_odd := ?_
    O_normal := ?_
    R_two := ?_
    R_comm := ?_
    y_mem := ?_
    y_sq := ?_
    alt_lift := ?_ }⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := hWrange g hg
    exact (mem_bcdLargeImg hn MB).2 ⟨q, hQB hq, hQo hq, MB.permX_of_mem (hQB hq)⟩
  · intro g hg
    obtain ⟨c, hcN, hcO, rfl⟩ := (mem_bcdLargeImg hn MB).1 hg
    exact (mem_bcdLargeImg hn MB).2 ⟨c, hcN, bcdLarge_oddCoreOf_le_oddTwoCoreOf D hcO, rfl⟩
  · exact (odd_card_oddCoreOf D).of_dvd_nat (card_bcdLargeImg_dvd hn MB (oddCoreOf D))
  · intro r hr o ho
    obtain ⟨c, hcN, hcR, rfl⟩ := (mem_bcdLargeImg hn MB).1 hr
    obtain ⟨c', hc'N, hc'O, rfl⟩ := (mem_bcdLargeImg hn MB).1 ho
    refine (mem_bcdLargeImg hn MB).2 ⟨c * c' * c⁻¹, mul_mem (mul_mem hcN hc'N) (inv_mem hcN),
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf D (oddTwoCoreOf_le D hcR)) c').1 hc'O,
      ?_⟩
    exact (MB.permX_conj hn hcN hc'N)
  · intro r hr
    obtain ⟨c, hcN, hcR, rfl⟩ := (mem_bcdLargeImg hn MB).1 hr
    obtain ⟨k, hk⟩ := oddTwoCoreOf_two D hcR
    refine ⟨k, (mem_bcdLargeImg hn MB).2 ⟨c ^ 2 ^ k, pow_mem hcN _, hk, ?_⟩⟩
    exact bcdLarge_permX_pow hn MB hcN _
  · intro r hr
    obtain ⟨c, hcN, hcR, rfl⟩ := (mem_bcdLargeImg hn MB).1 hr
    exact hcomm c hcR hcN
  · exact (mem_bcdLargeImg hn MB).2 ⟨y, hyN, hQo hyQ', rfl⟩
  · rw [← MB.permX_mul hn hyN hyN, hyy]
    exact hτx
  · intro π hπ
    obtain ⟨b, hb, hbτ, hbπ⟩ := exists_lift_alt_cycles hn MB huN hu2 π hπ
    have hbN : b ∈ normalizer (B : Set X) := Subgroup.le_normalizer hb.1
    have hbD : b ∈ D := hBD hb
    refine ⟨MB.permX b, hbτ, ?_, hbπ⟩
    intro r hr
    obtain ⟨c, hcN, hcR, rfl⟩ := (mem_bcdLargeImg hn MB).1 hr
    refine (mem_bcdLargeImg hn MB).2 ⟨b * c * b⁻¹, mul_mem (mul_mem hbN hcN) (inv_mem hbN),
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddTwoCoreOf D hbD) c).1 hcR, ?_⟩
    exact (MB.permX_conj hn hbN hcN)

end PermData

section Quat

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem quatPermDataM_of_multi (hn : 13 ≤ n) (h : Sec5Data X n z Z S) {s : X}
    (hs : IsSec5Inv X Z s) {u : X} (huZ : u ∈ Z) (hu1 : u ≠ 1) (hus : u * s = s * u)
    {Q : Subgroup X} (hQ2 : IsPGroup 2 ↥Q) (hQ8 : Nat.card ↥Q = 8) (huQ : u ∈ Q)
    (hQpow : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) (hyQ : ∃ y ∈ Q, y * y = u)
    (hQo : Q ≤ oddTwoCoreOf (centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X)))
    (hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X)) :
    Nonempty (QuatPermDataM n) := by
  have hn8 : 8 ≤ n := by omega
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
  have hQB : Q ≤ normalizer (B : Set X) := hQn B hB
  have huN : u ∈ normalizer (B : Set X) := hQB huQ
  have hBs : B ≤ centralizer ({s} : Set X) := hB.isPCompIn.1
  let MB : AhatModel X n B := AhatModel.ofCover hB.2
  exact bcdLarge_permData hn8 MB huN hu2 (perm_ne_one_of_mem_Z h hs huZ hu1 hus hB huN MB)
    (fixCount_perm_le_four_of_mem_Z h hs huZ hu1 hus hB huN MB)
    (D := centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X)) inf_le_left
    (fun b hb => ⟨hb.2, hBs hb.1⟩) hQ8 huQ hQpow hyQ hQo hQB

end Quat

end CFSG.OddStandard.Solomon75
