module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Existence

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_sq_mem {S T : Subgroup G} (hT : IsPGroup 2 T) (hST : S < T) :
    ∃ x ∈ T ⊓ Subgroup.normalizer (S : Set G), x ∉ S ∧ x ^ 2 ∈ S := by
  obtain ⟨y, hy, hyS⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT hST.le hST.ne
  have hex : ∃ k : ℕ, y ^ 2 ^ k ∈ S := by
    obtain ⟨k, hk⟩ := hT ⟨y, hy.1⟩
    refine ⟨k, ?_⟩
    have : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this]
    exact S.one_mem
  classical
  set m := Nat.find hex with hm
  have hm0 : m ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm, h0] at this
    exact hyS (by simpa using this)
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : y ^ 2 ^ m' ∉ S := Nat.find_min hex (by omega)
  refine ⟨y ^ 2 ^ m', ?_, hmin, ?_⟩
  · exact ⟨T.pow_mem hy.1 _, (Subgroup.normalizer (S : Set G)).pow_mem hy.2 _⟩
  · have := Nat.find_spec hex
    rw [← hm, hm', pow_succ, pow_mul] at this
    exact this

theorem exists_notation25 (h253 : Lemma253Component) {T M : Subgroup G}
    (hs : UnconstrainedSetting G T M) : Nonempty (Notation25 hs) := by
  obtain ⟨B, H, S, hB1, hB2, hHB, hU, hSM, hSH, hSc, hlt, -, -, hcentre, -, -⟩ :=
    exists_unconstrained_normalizer_configuration hs.setting hs.escaping hs.noCharTwo
  have hT2 : IsPGroup 2 T := hs.setting.isPGroup
  have hT1 : T ≠ ⊥ := ne_bot_of_le_ne_bot hSc.2.1 hlt.le
  have hZ1 : centerOf T ≠ ⊥ := inf_centralizer_ne_bot hT2 hT1
  obtain ⟨z, hzZ, hz1, hz2⟩ :=
    GammaExtra.exists_involution_of_ne_bot (hT2.to_le (inf_le_left : centerOf T ≤ T)) hZ1
  have htuple : Tuple25 T M H S z :=
    { gamma0 := Or.inl hU
      sylow_inf := hSM
      sylow := hSH
      center_le := fun w hw => (hcentre hw).1
      lt := hlt
      z_mem := hzZ
      z_ne_one := hz1
      z_sq := hz2 }
  obtain ⟨K, hKH, hKnb, hKK, hUK, -⟩ := h253 G T M H S z hs htuple 1 (fun _ => B)
    (fun _ => ⟨hHB ▸ Subgroup.le_normalizer, hB2⟩)
    (by simp [hHB])
  have hU' : IsGammaU M (K ⊔ S) := hUK hU
  obtain ⟨-, hSH', hSM', -, -⟩ := IsGamma0.overgroup_of_sylow_le hs.setting
    (Or.inl hU : IsGamma0 M H) hSM hU'.isGamma le_sup_right (Or.inr ⟨hU, hU'.1⟩)
  obtain ⟨x, hxTN, hxS, hx2⟩ := exists_mem_normalizer_not_mem_sq_mem hT2 hlt
  exact ⟨{ H := K ⊔ S
           S := S
           K := K
           z := z
           x := x
           tuple := ⟨Or.inl hU', hSM', hSH', fun w hw => (hcentre hw).1, hlt, hzZ, hz1, hz2⟩
           gammaU := hU'
           isComp := hKK
           nonBender := hKnb
           join := rfl
           x_mem := hxTN
           x_not_mem := hxS
           x_sq := hx2 }⟩

end Existence

structure EarlyStages : Prop where
  h252 : Lemma252
  h254 : Notation254
  h255 : Lemma255
  h256 : Lemma256
  h257 : Lemma257
  h258 : Lemma258
  h2510 : Lemma2510
  h2511 : Lemma2511
  h2512 : Lemma2512
  h2513 : Lemma2513

theorem EarlyStages.exists_lv2513 (hst : EarlyStages) {G : Type} [Group G] [Finite G]
    {T M : Subgroup G} {hs : UnconstrainedSetting G T M} (N : Notation25 hs) :
    ∃ t zK : G, Lv2513 N t zK := by
  have c252 : ComponentList M N.S N.z N.K := hst.h252 G T M N.H N.S N.z hs N.tuple N.K N.isComp
  have lv254 : Lv254 N := ⟨c252, hst.h254 G T M hs N c252⟩
  have lv255 : Lv255 N := ⟨lv254, hst.h255 G T M hs N⟩
  have lv256 : Lv256 N := ⟨lv255, hst.h256 G T M hs N lv255⟩
  have lv257 : Lv257 N := ⟨lv256, hst.h257 G T M hs N lv256⟩
  have lv258 : Lv258 N := ⟨lv257, hst.h258 G T M hs N lv257⟩
  have lv2510 : Lv2510 N := ⟨lv258, hst.h2510 G T M hs N⟩
  obtain ⟨t, zK, f2511⟩ := hst.h2511 G T M hs N lv2510
  have lv2511 : Lv2511 N t zK := ⟨lv2510, f2511⟩
  have lv2512 : Lv2512 N t zK := ⟨lv2511, hst.h2512 G T M hs N t zK lv2511⟩
  exact ⟨t, zK, ⟨lv2512, hst.h2513 G T M hs N t zK lv2512⟩⟩

theorem unconstrainedBranch_of_parts
    (h252 : Lemma252) (h253 : Lemma253Component) (h254 : Notation254) (h255 : Lemma255)
    (h256 : Lemma256) (h257 : Lemma257) (h258 : Lemma258) (h2510 : Lemma2510)
    (h2511 : Lemma2511) (h2512 : Lemma2512) (h2513 : Lemma2513) (h2515 : Lemma2515)
    (h2516 : Lemma2516) (h2518 : Lemma2518) (h2519 : Lemma2519) (h2520 : Lemma2520)
    (h2521 : Lemma2521) (h2522 : Lemma2522) (h2523 : Lemma2523) (h2524 : Lemma2524)
    (h2525 : Lemma2525) (h2526 : Lemma2526) (h2527 : Lemma2527) (hfinal : Lemma25Final) :
    UnconstrainedBranch := by
  intro G _ _ T M h hnb hns hδ hno
  have hs : UnconstrainedSetting G T M := ⟨h, hnb, hns, hδ, hno⟩
  obtain ⟨N⟩ := exists_notation25 h253 hs
  have c252 : ComponentList M N.S N.z N.K := h252 G T M N.H N.S N.z hs N.tuple N.K N.isComp
  have lv254 : Lv254 N := ⟨c252, h254 G T M hs N c252⟩
  have lv255 : Lv255 N := ⟨lv254, h255 G T M hs N⟩
  have lv256 : Lv256 N := ⟨lv255, h256 G T M hs N lv255⟩
  have lv257 : Lv257 N := ⟨lv256, h257 G T M hs N lv256⟩
  have lv258 : Lv258 N := ⟨lv257, h258 G T M hs N lv257⟩
  have lv2510 : Lv2510 N := ⟨lv258, h2510 G T M hs N⟩
  obtain ⟨t, zK, f2511⟩ := h2511 G T M hs N lv2510
  have lv2511 : Lv2511 N t zK := ⟨lv2510, f2511⟩
  have lv2512 : Lv2512 N t zK := ⟨lv2511, h2512 G T M hs N t zK lv2511⟩
  have lv2513 : Lv2513 N t zK := ⟨lv2512, h2513 G T M hs N t zK lv2512⟩
  have lv2515 : Lv2515 N t zK := ⟨lv2513, h2515 G T M hs N t zK lv2513⟩
  have lv2516 : Lv2516 N t zK := ⟨lv2515, h2516 G T M hs N t zK lv2515⟩
  have lv2518 : Lv2518 N t zK := ⟨lv2516, h2518 G T M hs N t zK lv2516⟩
  have lv2519 : Lv2519 N t zK := ⟨lv2518, h2519 G T M hs N t zK lv2518⟩
  have lv2520 : Lv2520 N t zK := ⟨lv2519, h2520 G T M hs N t zK lv2519⟩
  have lv2521 : Lv2521 N t zK := ⟨lv2520, h2521 G T M hs N t zK lv2520⟩
  have lv2522 : Lv2522 N t zK := ⟨lv2521, h2522 G T M hs N t zK lv2521⟩
  have lv2523 : Lv2523 N t zK := ⟨lv2522, h2523 G T M hs N t zK lv2522⟩
  have lv2524 : Lv2524 N t zK := ⟨lv2523, h2524 G T M hs N t zK lv2523⟩
  have lv2525 : Lv2525 N t zK := ⟨lv2524, h2525 G T M hs N t zK lv2524⟩
  have lv2526 : Lv2526 N t zK := ⟨lv2525, h2526 G T M hs N t zK lv2525⟩
  have lv2527 : Lv2527 N t zK := ⟨lv2526, h2527 G T M hs N t zK lv2526⟩
  exact hfinal G T M hs N t zK lv2527

end CFSG.QuasithinUnique
