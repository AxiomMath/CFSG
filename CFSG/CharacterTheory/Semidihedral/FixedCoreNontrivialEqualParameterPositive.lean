module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveFinal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocalPlus
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterTorus
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusSquare

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem EqualParameterData.positiveInputs
    {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G}
    {J : Subgroup G} {p f : ℕ} {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
    {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) : PositiveInputs G t s₀ d J p f where
  card_W_B := h.card_W_B
  card_sylow_two := h.card_sylow_two
  le_C_of_isPGroup := h.le_C_of_isPGroup
  exists_normal_complement_torus_core := h.exists_normal_complement_torus_core
  sylow_C_facts := h.sylow_C_facts
  eq_bot_of_mod_four_eq_one := h.eq_bot_of_mod_four_eq_one
  layer_le_of_not_le_normalizer := h.layer_le_of_not_le_normalizer
  exists_layer_torus := h.exists_layer_torus
  sylow_H_facts := h.sylow_H_facts
  exists_split_torus_sylow := h.exists_split_torus_sylow
  le_centralizer_of_isPGroup_two_of_no_kleinFour := le_centralizer_of_isPGroup_two_of_no_kleinFour
  conj_eq_inv_of_inf_centralizer_eq_bot := conj_eq_inv_of_inf_centralizer_eq_bot
  odd_mem_pPrimeCore_of_isCyclic_sylow := odd_mem_pPrimeCore_of_isCyclic_sylow
  sq_dvd_card_of_sl2_inverting := sq_dvd_card_of_sl2_inverting

theorem EqualParameterData.mod_four_ne_one
    {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G}
    {J : Subgroup G} {p f : ℕ} {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
    {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) : p ^ f % 4 ≠ 1 :=
  h.positiveInputs.mod_four_ne_one h

end CFSG.Semidihedral.FixedCoreNontrivial
